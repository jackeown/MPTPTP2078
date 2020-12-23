%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wZFW2uS3U

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:38 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  330 (77992 expanded)
%              Number of leaves         :   39 (22458 expanded)
%              Depth                    :   39
%              Number of atoms          : 2727 (1167426 expanded)
%              Number of equality atoms :  160 (61294 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ sk_C @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ sk_C @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['32','35','40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_C = sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','43'])).

thf('45',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_C = sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('48',plain,
    ( ( sk_C = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( sk_C = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('53',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_C = sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ( sk_C = sk_B )
    | ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['49','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('79',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('83',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('84',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_C = sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','99'])).

thf('101',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('102',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['107','111'])).

thf('113',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('115',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('118',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['112','115','118','121','124'])).

thf('126',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','99'])).

thf('127',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('129',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('131',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('138',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('139',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('140',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('141',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('143',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('146',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['139','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['165','166','167','168','169'])).

thf('171',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('172',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('174',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('176',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ( sk_A
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( sk_A
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','182'])).

thf('184',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('185',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188'])).

thf('190',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['189','198'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','204'])).

thf('206',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('208',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['129','207'])).

thf('209',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('210',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('213',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('214',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('215',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('216',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('218',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('222',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('224',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('226',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('227',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('228',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','229'])).

thf('231',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('232',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('233',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('235',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('236',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['224','225','230','233','236'])).

thf('238',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('239',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('241',plain,(
    r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['239','240'])).

thf('242',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('243',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('244',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('245',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['243','246'])).

thf('248',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','229'])).

thf('251',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0
          = ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['242','253'])).

thf('255',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('256',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['241','258'])).

thf('260',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['208','259'])).

thf('261',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('262',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('263',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','229'])).

thf('265',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('266',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('268',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('269',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('271',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simpl_trail,[status(thm)],['269','270'])).

thf('272',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['241','258'])).

thf('273',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('274',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('276',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('277',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['275','276'])).

thf('278',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','229'])).

thf('279',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('280',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('281',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('283',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('284',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['274','277','278','281','284'])).

thf('286',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['266','271','285'])).

thf('287',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','205','206'])).

thf('288',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simpl_trail,[status(thm)],['286','287'])).

thf('289',plain,(
    $false ),
    inference(demod,[status(thm)],['260','288'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wZFW2uS3U
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.51/2.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.51/2.70  % Solved by: fo/fo7.sh
% 2.51/2.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.51/2.70  % done 3318 iterations in 2.235s
% 2.51/2.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.51/2.70  % SZS output start Refutation
% 2.51/2.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.51/2.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.51/2.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.51/2.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.51/2.70  thf(sk_C_type, type, sk_C: $i).
% 2.51/2.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.51/2.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.51/2.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.51/2.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.51/2.70  thf(sk_A_type, type, sk_A: $i).
% 2.51/2.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.51/2.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.51/2.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.51/2.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.51/2.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.51/2.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.51/2.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.51/2.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.51/2.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.51/2.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.51/2.70  thf(sk_B_type, type, sk_B: $i).
% 2.51/2.70  thf(t31_funct_2, conjecture,
% 2.51/2.70    (![A:$i,B:$i,C:$i]:
% 2.51/2.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.51/2.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.51/2.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.51/2.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.51/2.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.51/2.70           ( m1_subset_1 @
% 2.51/2.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.51/2.70  thf(zf_stmt_0, negated_conjecture,
% 2.51/2.70    (~( ![A:$i,B:$i,C:$i]:
% 2.51/2.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.51/2.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.51/2.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.51/2.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.51/2.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.51/2.70              ( m1_subset_1 @
% 2.51/2.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.51/2.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.51/2.70  thf('0', plain,
% 2.51/2.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.51/2.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.51/2.70        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.51/2.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.51/2.70  thf('1', plain,
% 2.51/2.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.51/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.51/2.70      inference('split', [status(esa)], ['0'])).
% 2.51/2.70  thf(d1_funct_2, axiom,
% 2.51/2.70    (![A:$i,B:$i,C:$i]:
% 2.51/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.51/2.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.51/2.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.51/2.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.51/2.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.51/2.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.51/2.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.51/2.70  thf(zf_stmt_1, axiom,
% 2.51/2.70    (![B:$i,A:$i]:
% 2.51/2.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.51/2.70       ( zip_tseitin_0 @ B @ A ) ))).
% 2.51/2.70  thf('2', plain,
% 2.51/2.70      (![X25 : $i, X26 : $i]:
% 2.51/2.70         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.51/2.70  thf('3', plain,
% 2.51/2.70      (![X25 : $i, X26 : $i]:
% 2.51/2.70         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.51/2.70  thf(t113_zfmisc_1, axiom,
% 2.51/2.70    (![A:$i,B:$i]:
% 2.51/2.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.51/2.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.51/2.70  thf('4', plain,
% 2.51/2.70      (![X4 : $i, X5 : $i]:
% 2.51/2.70         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.51/2.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.51/2.70  thf('5', plain,
% 2.51/2.70      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.51/2.70      inference('simplify', [status(thm)], ['4'])).
% 2.51/2.70  thf('6', plain,
% 2.51/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.51/2.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.51/2.70      inference('sup+', [status(thm)], ['3', '5'])).
% 2.51/2.70  thf('7', plain,
% 2.51/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.51/2.70  thf('8', plain,
% 2.51/2.70      (![X0 : $i]:
% 2.51/2.70         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.51/2.70          | (zip_tseitin_0 @ sk_B @ X0))),
% 2.51/2.70      inference('sup+', [status(thm)], ['6', '7'])).
% 2.51/2.70  thf('9', plain,
% 2.51/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.51/2.70         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.51/2.70          | (zip_tseitin_0 @ X0 @ X2)
% 2.51/2.70          | (zip_tseitin_0 @ sk_B @ X1))),
% 2.51/2.70      inference('sup+', [status(thm)], ['2', '8'])).
% 2.51/2.70  thf('10', plain,
% 2.51/2.70      (![X0 : $i]:
% 2.51/2.70         ((zip_tseitin_0 @ sk_B @ X0)
% 2.51/2.70          | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))),
% 2.51/2.70      inference('eq_fact', [status(thm)], ['9'])).
% 2.51/2.70  thf(t3_subset, axiom,
% 2.51/2.70    (![A:$i,B:$i]:
% 2.51/2.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.51/2.70  thf('11', plain,
% 2.51/2.70      (![X6 : $i, X7 : $i]:
% 2.51/2.70         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.51/2.70      inference('cnf', [status(esa)], [t3_subset])).
% 2.51/2.70  thf('12', plain,
% 2.51/2.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 2.51/2.70      inference('sup-', [status(thm)], ['10', '11'])).
% 2.51/2.70  thf('13', plain,
% 2.51/2.70      (![X0 : $i]:
% 2.51/2.70         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.51/2.70          | (zip_tseitin_0 @ sk_B @ X0))),
% 2.51/2.70      inference('sup+', [status(thm)], ['6', '7'])).
% 2.51/2.70  thf('14', plain,
% 2.51/2.70      (![X4 : $i, X5 : $i]:
% 2.51/2.70         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.51/2.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.51/2.70  thf('15', plain,
% 2.51/2.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.51/2.70      inference('simplify', [status(thm)], ['14'])).
% 2.51/2.70  thf(cc2_relset_1, axiom,
% 2.51/2.70    (![A:$i,B:$i,C:$i]:
% 2.51/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.51/2.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.51/2.70  thf('16', plain,
% 2.51/2.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.51/2.70         ((v5_relat_1 @ X16 @ X18)
% 2.51/2.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.51/2.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.51/2.70  thf('17', plain,
% 2.51/2.70      (![X0 : $i, X1 : $i]:
% 2.51/2.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.51/2.70          | (v5_relat_1 @ X1 @ X0))),
% 2.51/2.70      inference('sup-', [status(thm)], ['15', '16'])).
% 2.51/2.70  thf('18', plain,
% 2.51/2.70      (![X0 : $i, X1 : $i]:
% 2.51/2.70         ((zip_tseitin_0 @ sk_B @ X1) | (v5_relat_1 @ sk_C @ X0))),
% 2.51/2.70      inference('sup-', [status(thm)], ['13', '17'])).
% 2.51/2.70  thf('19', plain,
% 2.51/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.51/2.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.51/2.70  thf(zf_stmt_3, axiom,
% 2.51/2.70    (![C:$i,B:$i,A:$i]:
% 2.51/2.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.51/2.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.51/2.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.51/2.70  thf(zf_stmt_5, axiom,
% 2.51/2.70    (![A:$i,B:$i,C:$i]:
% 2.51/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.51/2.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.51/2.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.51/2.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.51/2.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.51/2.70  thf('20', plain,
% 2.51/2.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.51/2.70         (~ (zip_tseitin_0 @ X30 @ X31)
% 2.51/2.70          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 2.51/2.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.51/2.70  thf('21', plain,
% 2.51/2.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.51/2.70      inference('sup-', [status(thm)], ['19', '20'])).
% 2.51/2.70  thf('22', plain,
% 2.51/2.70      (![X0 : $i]:
% 2.51/2.70         ((v5_relat_1 @ sk_C @ X0) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.51/2.70      inference('sup-', [status(thm)], ['18', '21'])).
% 2.51/2.70  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.51/2.70  thf('24', plain,
% 2.51/2.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.51/2.70         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 2.51/2.70          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 2.51/2.70          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.51/2.70  thf('25', plain,
% 2.51/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.51/2.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.51/2.70      inference('sup-', [status(thm)], ['23', '24'])).
% 2.51/2.70  thf('26', plain,
% 2.51/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.51/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.51/2.70  thf(redefinition_k1_relset_1, axiom,
% 2.51/2.70    (![A:$i,B:$i,C:$i]:
% 2.51/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.51/2.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.51/2.70  thf('27', plain,
% 2.51/2.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.51/2.70         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 2.51/2.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.51/2.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.51/2.70  thf('28', plain,
% 2.51/2.70      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.51/2.70      inference('sup-', [status(thm)], ['26', '27'])).
% 2.51/2.70  thf('29', plain,
% 2.51/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.51/2.70      inference('demod', [status(thm)], ['25', '28'])).
% 2.51/2.70  thf('30', plain,
% 2.51/2.70      (![X0 : $i]: ((v5_relat_1 @ sk_C @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.51/2.70      inference('sup-', [status(thm)], ['22', '29'])).
% 2.51/2.70  thf(d19_relat_1, axiom,
% 2.51/2.70    (![A:$i,B:$i]:
% 2.51/2.70     ( ( v1_relat_1 @ B ) =>
% 2.51/2.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.51/2.70  thf('31', plain,
% 2.51/2.70      (![X9 : $i, X10 : $i]:
% 2.51/2.70         (~ (v5_relat_1 @ X9 @ X10)
% 2.51/2.70          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 2.51/2.70          | ~ (v1_relat_1 @ X9))),
% 2.51/2.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.51/2.70  thf('32', plain,
% 2.51/2.70      (![X0 : $i]:
% 2.51/2.70         (((sk_A) = (k1_relat_1 @ sk_C))
% 2.51/2.70          | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['30', '31'])).
% 2.52/2.70  thf('33', plain,
% 2.52/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf(cc1_relset_1, axiom,
% 2.52/2.70    (![A:$i,B:$i,C:$i]:
% 2.52/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.52/2.70       ( v1_relat_1 @ C ) ))).
% 2.52/2.70  thf('34', plain,
% 2.52/2.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.52/2.70         ((v1_relat_1 @ X13)
% 2.52/2.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.52/2.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.52/2.70  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('36', plain,
% 2.52/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf(redefinition_k2_relset_1, axiom,
% 2.52/2.70    (![A:$i,B:$i,C:$i]:
% 2.52/2.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.52/2.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.52/2.70  thf('37', plain,
% 2.52/2.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.52/2.70         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 2.52/2.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.52/2.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.52/2.70  thf('38', plain,
% 2.52/2.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.52/2.70      inference('sup-', [status(thm)], ['36', '37'])).
% 2.52/2.70  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('40', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.52/2.70      inference('sup+', [status(thm)], ['38', '39'])).
% 2.52/2.70  thf('41', plain,
% 2.52/2.70      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | (r1_tarski @ sk_B @ X0))),
% 2.52/2.70      inference('demod', [status(thm)], ['32', '35', '40'])).
% 2.52/2.70  thf(d10_xboole_0, axiom,
% 2.52/2.70    (![A:$i,B:$i]:
% 2.52/2.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.52/2.70  thf('42', plain,
% 2.52/2.70      (![X0 : $i, X2 : $i]:
% 2.52/2.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.52/2.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.70  thf('43', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (((sk_A) = (k1_relat_1 @ sk_C))
% 2.52/2.70          | ~ (r1_tarski @ X0 @ sk_B)
% 2.52/2.70          | ((X0) = (sk_B)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['41', '42'])).
% 2.52/2.70  thf('44', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((zip_tseitin_0 @ sk_B @ X0)
% 2.52/2.70          | ((sk_C) = (sk_B))
% 2.52/2.70          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['12', '43'])).
% 2.52/2.70  thf('45', plain,
% 2.52/2.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['19', '20'])).
% 2.52/2.70  thf('46', plain,
% 2.52/2.70      ((((sk_A) = (k1_relat_1 @ sk_C))
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['44', '45'])).
% 2.52/2.70  thf('47', plain,
% 2.52/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['25', '28'])).
% 2.52/2.70  thf('48', plain, ((((sk_C) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('clc', [status(thm)], ['46', '47'])).
% 2.52/2.70  thf(t55_funct_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.52/2.70       ( ( v2_funct_1 @ A ) =>
% 2.52/2.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.52/2.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.52/2.70  thf('49', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('50', plain, ((((sk_C) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('clc', [status(thm)], ['46', '47'])).
% 2.52/2.70  thf(dt_k2_funct_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.52/2.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.52/2.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.52/2.70  thf('51', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('52', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('53', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('54', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.52/2.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.70  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf('56', plain,
% 2.52/2.70      (![X9 : $i, X10 : $i]:
% 2.52/2.70         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 2.52/2.70          | (v5_relat_1 @ X9 @ X10)
% 2.52/2.70          | ~ (v1_relat_1 @ X9))),
% 2.52/2.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.52/2.70  thf('57', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['55', '56'])).
% 2.52/2.70  thf('58', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['53', '57'])).
% 2.52/2.70  thf('59', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['52', '58'])).
% 2.52/2.70  thf('60', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['59'])).
% 2.52/2.70  thf('61', plain,
% 2.52/2.70      (![X9 : $i, X10 : $i]:
% 2.52/2.70         (~ (v5_relat_1 @ X9 @ X10)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 2.52/2.70          | ~ (v1_relat_1 @ X9))),
% 2.52/2.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.52/2.70  thf('62', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['60', '61'])).
% 2.52/2.70  thf('63', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['51', '62'])).
% 2.52/2.70  thf('64', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X0)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['63'])).
% 2.52/2.70  thf('65', plain,
% 2.52/2.70      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70        | ~ (v2_funct_1 @ sk_C))),
% 2.52/2.70      inference('sup+', [status(thm)], ['50', '64'])).
% 2.52/2.70  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('69', plain,
% 2.52/2.70      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.52/2.70        | ((sk_C) = (sk_B)))),
% 2.52/2.70      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 2.52/2.70  thf('70', plain,
% 2.52/2.70      (![X0 : $i, X2 : $i]:
% 2.52/2.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.52/2.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.70  thf('71', plain,
% 2.52/2.70      ((((sk_C) = (sk_B))
% 2.52/2.70        | ~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.52/2.70        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['69', '70'])).
% 2.52/2.70  thf('72', plain,
% 2.52/2.70      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.52/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70        | ~ (v2_funct_1 @ sk_C)
% 2.52/2.70        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.52/2.70        | ((sk_C) = (sk_B)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['49', '71'])).
% 2.52/2.70  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('76', plain,
% 2.52/2.70      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.52/2.70        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.52/2.70        | ((sk_C) = (sk_B)))),
% 2.52/2.70      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 2.52/2.70  thf('77', plain,
% 2.52/2.70      ((~ (r1_tarski @ sk_A @ sk_A)
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['48', '76'])).
% 2.52/2.70  thf('78', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf('79', plain,
% 2.52/2.70      ((((sk_C) = (sk_B))
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('demod', [status(thm)], ['77', '78'])).
% 2.52/2.70  thf('80', plain,
% 2.52/2.70      ((((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))) | ((sk_C) = (sk_B)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['79'])).
% 2.52/2.70  thf('81', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('82', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('83', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('84', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf(t4_funct_2, axiom,
% 2.52/2.70    (![A:$i,B:$i]:
% 2.52/2.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.52/2.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.52/2.70         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 2.52/2.70           ( m1_subset_1 @
% 2.52/2.70             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 2.52/2.70  thf('85', plain,
% 2.52/2.70      (![X33 : $i, X34 : $i]:
% 2.52/2.70         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 2.52/2.70          | (v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ X34)
% 2.52/2.70          | ~ (v1_funct_1 @ X33)
% 2.52/2.70          | ~ (v1_relat_1 @ X33))),
% 2.52/2.70      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.52/2.70  thf('86', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['84', '85'])).
% 2.52/2.70  thf('87', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['83', '86'])).
% 2.52/2.70  thf('88', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['82', '87'])).
% 2.52/2.70  thf('89', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['88'])).
% 2.52/2.70  thf('90', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['81', '89'])).
% 2.52/2.70  thf('91', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['90'])).
% 2.52/2.70  thf('92', plain,
% 2.52/2.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 2.52/2.70        | ((sk_C) = (sk_B))
% 2.52/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70        | ~ (v2_funct_1 @ sk_C))),
% 2.52/2.70      inference('sup+', [status(thm)], ['80', '91'])).
% 2.52/2.70  thf('93', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.52/2.70      inference('sup+', [status(thm)], ['38', '39'])).
% 2.52/2.70  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('97', plain,
% 2.52/2.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_C) = (sk_B)))),
% 2.52/2.70      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 2.52/2.70  thf('98', plain,
% 2.52/2.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('99', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('100', plain,
% 2.52/2.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['1', '99'])).
% 2.52/2.70  thf('101', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('102', plain,
% 2.52/2.70      (![X25 : $i, X26 : $i]:
% 2.52/2.70         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.52/2.70  thf('103', plain,
% 2.52/2.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['19', '20'])).
% 2.52/2.70  thf('104', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['102', '103'])).
% 2.52/2.70  thf('105', plain,
% 2.52/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['25', '28'])).
% 2.52/2.70  thf('106', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['104', '105'])).
% 2.52/2.70  thf('107', plain,
% 2.52/2.70      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['101', '106'])).
% 2.52/2.70  thf('108', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('109', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['90'])).
% 2.52/2.70  thf('110', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70           (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0))),
% 2.52/2.70      inference('sup+', [status(thm)], ['108', '109'])).
% 2.52/2.70  thf('111', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.52/2.70             (k1_relat_1 @ X0)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['110'])).
% 2.52/2.70  thf('112', plain,
% 2.52/2.70      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.52/2.70         | ((sk_B) = (k1_xboole_0))
% 2.52/2.70         | ~ (v1_relat_1 @ sk_B)
% 2.52/2.70         | ~ (v1_funct_1 @ sk_B)
% 2.52/2.70         | ~ (v2_funct_1 @ sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['107', '111'])).
% 2.52/2.70  thf('113', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('114', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.52/2.70      inference('sup+', [status(thm)], ['38', '39'])).
% 2.52/2.70  thf('115', plain,
% 2.52/2.70      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['113', '114'])).
% 2.52/2.70  thf('116', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('118', plain,
% 2.52/2.70      (((v1_relat_1 @ sk_B))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['116', '117'])).
% 2.52/2.70  thf('119', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('121', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_B))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['119', '120'])).
% 2.52/2.70  thf('122', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('124', plain,
% 2.52/2.70      (((v2_funct_1 @ sk_B))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['122', '123'])).
% 2.52/2.70  thf('125', plain,
% 2.52/2.70      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 2.52/2.70         | ((sk_B) = (k1_xboole_0))))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['112', '115', '118', '121', '124'])).
% 2.52/2.70  thf('126', plain,
% 2.52/2.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['1', '99'])).
% 2.52/2.70  thf('127', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('128', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('129', plain,
% 2.52/2.70      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['100', '127', '128'])).
% 2.52/2.70  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('131', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('132', plain,
% 2.52/2.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.52/2.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('133', plain,
% 2.52/2.70      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.52/2.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['131', '132'])).
% 2.52/2.70  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('135', plain,
% 2.52/2.70      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.52/2.70      inference('demod', [status(thm)], ['133', '134'])).
% 2.52/2.70  thf('136', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['130', '135'])).
% 2.52/2.70  thf('137', plain,
% 2.52/2.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('138', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('139', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('140', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('141', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('142', plain,
% 2.52/2.70      (![X25 : $i, X26 : $i]:
% 2.52/2.70         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.52/2.70  thf('143', plain,
% 2.52/2.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['14'])).
% 2.52/2.70  thf('144', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.52/2.70      inference('sup+', [status(thm)], ['142', '143'])).
% 2.52/2.70  thf('145', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf('146', plain,
% 2.52/2.70      (![X33 : $i, X34 : $i]:
% 2.52/2.70         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 2.52/2.70          | (m1_subset_1 @ X33 @ 
% 2.52/2.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ X34)))
% 2.52/2.70          | ~ (v1_funct_1 @ X33)
% 2.52/2.70          | ~ (v1_relat_1 @ X33))),
% 2.52/2.70      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.52/2.70  thf('147', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | (m1_subset_1 @ X0 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['145', '146'])).
% 2.52/2.70  thf('148', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i]:
% 2.52/2.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.52/2.70          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('sup+', [status(thm)], ['144', '147'])).
% 2.52/2.70  thf('149', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.52/2.70      inference('sup+', [status(thm)], ['142', '143'])).
% 2.52/2.70  thf('150', plain,
% 2.52/2.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['19', '20'])).
% 2.52/2.70  thf('151', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.52/2.70          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['149', '150'])).
% 2.52/2.70  thf('152', plain,
% 2.52/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['25', '28'])).
% 2.52/2.70  thf('153', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.52/2.70          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['151', '152'])).
% 2.52/2.70  thf('154', plain,
% 2.52/2.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('155', plain,
% 2.52/2.70      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.52/2.70         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['153', '154'])).
% 2.52/2.70  thf('156', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.52/2.70           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.52/2.70           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.52/2.70           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['148', '155'])).
% 2.52/2.70  thf('157', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (v1_relat_1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70           | ((sk_A) = (k1_relat_1 @ sk_C))
% 2.52/2.70           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['141', '156'])).
% 2.52/2.70  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('160', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (((sk_A) = (k1_relat_1 @ sk_C))
% 2.52/2.70           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)], ['157', '158', '159'])).
% 2.52/2.70  thf('161', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (v1_relat_1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.52/2.70           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['140', '160'])).
% 2.52/2.70  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('164', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.52/2.70           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)], ['161', '162', '163'])).
% 2.52/2.70  thf('165', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 2.52/2.70           | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70           | ~ (v2_funct_1 @ sk_C)
% 2.52/2.70           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup+', [status(thm)], ['139', '164'])).
% 2.52/2.70  thf('166', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.52/2.70      inference('sup+', [status(thm)], ['38', '39'])).
% 2.52/2.70  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('170', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)], ['165', '166', '167', '168', '169'])).
% 2.52/2.70  thf('171', plain,
% 2.52/2.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['19', '20'])).
% 2.52/2.70  thf('172', plain,
% 2.52/2.70      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['170', '171'])).
% 2.52/2.70  thf('173', plain,
% 2.52/2.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['25', '28'])).
% 2.52/2.70  thf('174', plain,
% 2.52/2.70      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('clc', [status(thm)], ['172', '173'])).
% 2.52/2.70  thf('175', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X0)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['63'])).
% 2.52/2.70  thf('176', plain,
% 2.52/2.70      ((((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.52/2.70         | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70         | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70         | ~ (v2_funct_1 @ sk_C)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup+', [status(thm)], ['174', '175'])).
% 2.52/2.70  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('180', plain,
% 2.52/2.70      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 2.52/2.70  thf('181', plain,
% 2.52/2.70      (![X0 : $i, X2 : $i]:
% 2.52/2.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.52/2.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.70  thf('182', plain,
% 2.52/2.70      (((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.52/2.70         | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['180', '181'])).
% 2.52/2.70  thf('183', plain,
% 2.52/2.70      (((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.52/2.70         | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70         | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70         | ~ (v2_funct_1 @ sk_C)
% 2.52/2.70         | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['138', '182'])).
% 2.52/2.70  thf('184', plain,
% 2.52/2.70      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('clc', [status(thm)], ['172', '173'])).
% 2.52/2.70  thf('185', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('189', plain,
% 2.52/2.70      ((((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)],
% 2.52/2.70                ['183', '184', '185', '186', '187', '188'])).
% 2.52/2.70  thf('190', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('191', plain,
% 2.52/2.70      (![X11 : $i]:
% 2.52/2.70         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.52/2.70          | ~ (v1_funct_1 @ X11)
% 2.52/2.70          | ~ (v1_relat_1 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.52/2.70  thf('192', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('193', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | (m1_subset_1 @ X0 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['145', '146'])).
% 2.52/2.70  thf('194', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['192', '193'])).
% 2.52/2.70  thf('195', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.52/2.70               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['191', '194'])).
% 2.52/2.70  thf('196', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['195'])).
% 2.52/2.70  thf('197', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.52/2.70               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['190', '196'])).
% 2.52/2.70  thf('198', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['197'])).
% 2.52/2.70  thf('199', plain,
% 2.52/2.70      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 2.52/2.70         | ~ (v1_relat_1 @ sk_C)
% 2.52/2.70         | ~ (v1_funct_1 @ sk_C)
% 2.52/2.70         | ~ (v2_funct_1 @ sk_C)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('sup+', [status(thm)], ['189', '198'])).
% 2.52/2.70  thf('200', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.52/2.70      inference('sup+', [status(thm)], ['38', '39'])).
% 2.52/2.70  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 2.52/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.70  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('204', plain,
% 2.52/2.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.52/2.70      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 2.52/2.70  thf('205', plain,
% 2.52/2.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.52/2.70      inference('demod', [status(thm)], ['137', '204'])).
% 2.52/2.70  thf('206', plain,
% 2.52/2.70      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.52/2.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.52/2.70       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('207', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('208', plain,
% 2.52/2.70      (~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['129', '207'])).
% 2.52/2.70  thf('209', plain,
% 2.52/2.70      ((((sk_C) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['97', '98'])).
% 2.52/2.70  thf('210', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('211', plain,
% 2.52/2.70      ((((k2_relset_1 @ sk_A @ sk_B @ sk_B) = (sk_B)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['209', '210'])).
% 2.52/2.70  thf('212', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('213', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('214', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.52/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.52/2.70  thf('215', plain,
% 2.52/2.70      (![X6 : $i, X8 : $i]:
% 2.52/2.70         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.52/2.70      inference('cnf', [status(esa)], [t3_subset])).
% 2.52/2.70  thf('216', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['214', '215'])).
% 2.52/2.70  thf('217', plain,
% 2.52/2.70      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['4'])).
% 2.52/2.70  thf('218', plain,
% 2.52/2.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.52/2.70         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 2.52/2.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.52/2.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.52/2.70  thf('219', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.52/2.70          | ((k2_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k2_relat_1 @ X1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['217', '218'])).
% 2.52/2.70  thf('220', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 2.52/2.70           = (k2_relat_1 @ k1_xboole_0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['216', '219'])).
% 2.52/2.70  thf('221', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('222', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('223', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.52/2.70          | ~ (v2_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_funct_1 @ X0)
% 2.52/2.70          | ~ (v1_relat_1 @ X0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['197'])).
% 2.52/2.70  thf('224', plain,
% 2.52/2.70      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.52/2.70          (k1_zfmisc_1 @ 
% 2.52/2.70           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 2.52/2.70            (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 2.52/2.70         | ~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.70         | ~ (v1_funct_1 @ k1_xboole_0)
% 2.52/2.70         | ~ (v2_funct_1 @ k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['222', '223'])).
% 2.52/2.70  thf('225', plain,
% 2.52/2.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['14'])).
% 2.52/2.70  thf('226', plain,
% 2.52/2.70      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['4'])).
% 2.52/2.70  thf('227', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['214', '215'])).
% 2.52/2.70  thf('228', plain,
% 2.52/2.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.52/2.70         ((v1_relat_1 @ X13)
% 2.52/2.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.52/2.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.52/2.70  thf('229', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['227', '228'])).
% 2.52/2.70  thf('230', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.70      inference('sup+', [status(thm)], ['226', '229'])).
% 2.52/2.70  thf('231', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_B))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['119', '120'])).
% 2.52/2.70  thf('232', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('233', plain,
% 2.52/2.70      (((v1_funct_1 @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['231', '232'])).
% 2.52/2.70  thf('234', plain,
% 2.52/2.70      (((v2_funct_1 @ sk_B))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['122', '123'])).
% 2.52/2.70  thf('235', plain,
% 2.52/2.70      ((((sk_B) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('clc', [status(thm)], ['125', '126'])).
% 2.52/2.70  thf('236', plain,
% 2.52/2.70      (((v2_funct_1 @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['234', '235'])).
% 2.52/2.70  thf('237', plain,
% 2.52/2.70      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['224', '225', '230', '233', '236'])).
% 2.52/2.70  thf('238', plain,
% 2.52/2.70      (![X6 : $i, X7 : $i]:
% 2.52/2.70         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.52/2.70      inference('cnf', [status(esa)], [t3_subset])).
% 2.52/2.70  thf('239', plain,
% 2.52/2.70      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['237', '238'])).
% 2.52/2.70  thf('240', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('241', plain, ((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['239', '240'])).
% 2.52/2.70  thf('242', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('243', plain,
% 2.52/2.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.52/2.70      inference('simplify', [status(thm)], ['14'])).
% 2.52/2.70  thf('244', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['214', '215'])).
% 2.52/2.70  thf('245', plain,
% 2.52/2.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.52/2.70         ((v5_relat_1 @ X16 @ X18)
% 2.52/2.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.52/2.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.52/2.70  thf('246', plain,
% 2.52/2.70      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 2.52/2.70      inference('sup-', [status(thm)], ['244', '245'])).
% 2.52/2.70  thf('247', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 2.52/2.70      inference('sup+', [status(thm)], ['243', '246'])).
% 2.52/2.70  thf('248', plain,
% 2.52/2.70      (![X9 : $i, X10 : $i]:
% 2.52/2.70         (~ (v5_relat_1 @ X9 @ X10)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 2.52/2.70          | ~ (v1_relat_1 @ X9))),
% 2.52/2.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.52/2.70  thf('249', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.70          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['247', '248'])).
% 2.52/2.70  thf('250', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.70      inference('sup+', [status(thm)], ['226', '229'])).
% 2.52/2.70  thf('251', plain,
% 2.52/2.70      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.52/2.70      inference('demod', [status(thm)], ['249', '250'])).
% 2.52/2.70  thf('252', plain,
% 2.52/2.70      (![X0 : $i, X2 : $i]:
% 2.52/2.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.52/2.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.70  thf('253', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         (~ (r1_tarski @ X0 @ (k2_relat_1 @ k1_xboole_0))
% 2.52/2.70          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['251', '252'])).
% 2.52/2.70  thf('254', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 2.52/2.70           | ((X0) = (k2_relat_1 @ k1_xboole_0))))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['242', '253'])).
% 2.52/2.70  thf('255', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('256', plain,
% 2.52/2.70      ((![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0))))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['254', '255'])).
% 2.52/2.70  thf('257', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('258', plain,
% 2.52/2.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['256', '257'])).
% 2.52/2.70  thf('259', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['241', '258'])).
% 2.52/2.70  thf('260', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)),
% 2.52/2.70      inference('demod', [status(thm)], ['208', '259'])).
% 2.52/2.70  thf('261', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('262', plain,
% 2.52/2.70      (![X33 : $i, X34 : $i]:
% 2.52/2.70         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 2.52/2.70          | (v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ X34)
% 2.52/2.70          | ~ (v1_funct_1 @ X33)
% 2.52/2.70          | ~ (v1_relat_1 @ X33))),
% 2.52/2.70      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.52/2.70  thf('263', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.52/2.70           | ~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.70           | ~ (v1_funct_1 @ k1_xboole_0)
% 2.52/2.70           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['261', '262'])).
% 2.52/2.70  thf('264', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.70      inference('sup+', [status(thm)], ['226', '229'])).
% 2.52/2.70  thf('265', plain,
% 2.52/2.70      (((v1_funct_1 @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['231', '232'])).
% 2.52/2.70  thf('266', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.52/2.70           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['263', '264', '265'])).
% 2.52/2.70  thf('267', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('268', plain,
% 2.52/2.70      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.52/2.70      inference('demod', [status(thm)], ['249', '250'])).
% 2.52/2.70  thf('269', plain,
% 2.52/2.70      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('sup+', [status(thm)], ['267', '268'])).
% 2.52/2.70  thf('270', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('271', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['269', '270'])).
% 2.52/2.70  thf('272', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('sup-', [status(thm)], ['241', '258'])).
% 2.52/2.70  thf('273', plain,
% 2.52/2.70      (![X12 : $i]:
% 2.52/2.70         (~ (v2_funct_1 @ X12)
% 2.52/2.70          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.52/2.70          | ~ (v1_funct_1 @ X12)
% 2.52/2.70          | ~ (v1_relat_1 @ X12))),
% 2.52/2.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.52/2.70  thf('274', plain,
% 2.52/2.70      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.52/2.70        | ~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.70        | ~ (v1_funct_1 @ k1_xboole_0)
% 2.52/2.70        | ~ (v2_funct_1 @ k1_xboole_0))),
% 2.52/2.70      inference('sup+', [status(thm)], ['272', '273'])).
% 2.52/2.70  thf('275', plain,
% 2.52/2.70      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.52/2.70  thf('276', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('277', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['275', '276'])).
% 2.52/2.70  thf('278', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.70      inference('sup+', [status(thm)], ['226', '229'])).
% 2.52/2.70  thf('279', plain,
% 2.52/2.70      (((v1_funct_1 @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['231', '232'])).
% 2.52/2.70  thf('280', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('281', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['279', '280'])).
% 2.52/2.70  thf('282', plain,
% 2.52/2.70      (((v2_funct_1 @ k1_xboole_0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['234', '235'])).
% 2.52/2.70  thf('283', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('284', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['282', '283'])).
% 2.52/2.70  thf('285', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.70      inference('demod', [status(thm)], ['274', '277', '278', '281', '284'])).
% 2.52/2.70  thf('286', plain,
% 2.52/2.70      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 2.52/2.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.52/2.70      inference('demod', [status(thm)], ['266', '271', '285'])).
% 2.52/2.70  thf('287', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.52/2.70      inference('sat_resolution*', [status(thm)], ['136', '205', '206'])).
% 2.52/2.70  thf('288', plain,
% 2.52/2.70      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.52/2.70      inference('simpl_trail', [status(thm)], ['286', '287'])).
% 2.52/2.70  thf('289', plain, ($false), inference('demod', [status(thm)], ['260', '288'])).
% 2.52/2.70  
% 2.52/2.70  % SZS output end Refutation
% 2.52/2.70  
% 2.52/2.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
