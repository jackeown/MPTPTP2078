%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1TTTMrjQJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  221 (2345 expanded)
%              Number of leaves         :   51 ( 727 expanded)
%              Depth                    :   31
%              Number of atoms          : 1551 (36994 expanded)
%              Number of equality atoms :  109 (1428 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( m1_subset_1 @ ( sk_C @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    ! [X46: $i,X47: $i] :
      ( v1_funct_2 @ ( sk_C @ X46 @ X47 ) @ X47 @ X46 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('37',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('50',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k9_relat_1 @ X24 @ X25 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X24 ) @ X25 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('60',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('65',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('77',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('78',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X48: $i] :
      ( ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('83',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('85',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('86',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('87',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['83','84','85','91'])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('95',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','97'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C_1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('109',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('110',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('111',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','107','108','109','110'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('113',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','111','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','117'])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ ( sk_C @ sk_A @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( sk_C @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','119'])).

thf('121',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('124',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','124','125'])).

thf('127',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('130',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('133',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('141',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('143',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('144',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ X0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','146'])).

thf('148',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('149',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('150',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('151',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('153',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152'])).

thf('154',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','153'])).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('158',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','124','125'])).

thf('160',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['128','160'])).

thf('162',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('165',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('166',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('167',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['127','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1TTTMrjQJ
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:36:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.03/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.22  % Solved by: fo/fo7.sh
% 1.03/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.22  % done 1161 iterations in 0.767s
% 1.03/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.22  % SZS output start Refutation
% 1.03/1.22  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.03/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.22  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.03/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.22  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.03/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.22  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.22  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.03/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.22  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.03/1.22  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.03/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.22  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.03/1.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.22  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.03/1.22  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.03/1.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.22  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.22  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.22  thf(t31_funct_2, conjecture,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.22       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.03/1.22         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.03/1.22           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.03/1.22           ( m1_subset_1 @
% 1.03/1.22             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.03/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.22    (~( ![A:$i,B:$i,C:$i]:
% 1.03/1.22        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.22            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.22          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.03/1.22            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.03/1.22              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.03/1.22              ( m1_subset_1 @
% 1.03/1.22                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.03/1.22    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.03/1.22  thf('0', plain,
% 1.03/1.22      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.03/1.22        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 1.03/1.22        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('1', plain,
% 1.03/1.22      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('2', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(cc1_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( v1_relat_1 @ C ) ))).
% 1.03/1.22  thf('3', plain,
% 1.03/1.22      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.22         ((v1_relat_1 @ X29)
% 1.03/1.22          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.03/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.22  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf(d9_funct_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.22       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.03/1.22  thf('5', plain,
% 1.03/1.22      (![X20 : $i]:
% 1.03/1.22         (~ (v2_funct_1 @ X20)
% 1.03/1.22          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 1.03/1.22          | ~ (v1_funct_1 @ X20)
% 1.03/1.22          | ~ (v1_relat_1 @ X20))),
% 1.03/1.22      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.03/1.22  thf('6', plain,
% 1.03/1.22      ((~ (v1_funct_1 @ sk_C_1)
% 1.03/1.22        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 1.03/1.22        | ~ (v2_funct_1 @ sk_C_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.03/1.22  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('8', plain, ((v2_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('9', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf('10', plain,
% 1.03/1.22      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.03/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('demod', [status(thm)], ['1', '9'])).
% 1.03/1.22  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf(dt_k2_funct_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.22       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.03/1.22         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.03/1.22  thf('12', plain,
% 1.03/1.22      (![X21 : $i]:
% 1.03/1.22         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.03/1.22          | ~ (v1_funct_1 @ X21)
% 1.03/1.22          | ~ (v1_relat_1 @ X21))),
% 1.03/1.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.22  thf('13', plain,
% 1.03/1.22      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.03/1.22         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('14', plain,
% 1.03/1.22      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 1.03/1.22         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('16', plain,
% 1.03/1.22      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.03/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.03/1.22  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['11', '16'])).
% 1.03/1.22  thf(t113_zfmisc_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.03/1.22       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.03/1.22  thf('18', plain,
% 1.03/1.22      (![X5 : $i, X6 : $i]:
% 1.03/1.22         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.03/1.22  thf('19', plain,
% 1.03/1.22      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.03/1.22      inference('simplify', [status(thm)], ['18'])).
% 1.03/1.22  thf(rc1_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ?[C:$i]:
% 1.03/1.22       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 1.03/1.22         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 1.03/1.22         ( v1_relat_1 @ C ) & 
% 1.03/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.03/1.22  thf('20', plain,
% 1.03/1.22      (![X46 : $i, X47 : $i]:
% 1.03/1.22         (m1_subset_1 @ (sk_C @ X46 @ X47) @ 
% 1.03/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))),
% 1.03/1.22      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.03/1.22  thf('21', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (m1_subset_1 @ (sk_C @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.03/1.22      inference('sup+', [status(thm)], ['19', '20'])).
% 1.03/1.22  thf(t3_subset, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.03/1.22  thf('22', plain,
% 1.03/1.22      (![X8 : $i, X9 : $i]:
% 1.03/1.22         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.03/1.22  thf('23', plain,
% 1.03/1.22      (![X0 : $i]: (r1_tarski @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['21', '22'])).
% 1.03/1.22  thf(t4_subset_1, axiom,
% 1.03/1.22    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.03/1.22  thf('24', plain,
% 1.03/1.22      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.03/1.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.03/1.22  thf('25', plain,
% 1.03/1.22      (![X8 : $i, X9 : $i]:
% 1.03/1.22         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.03/1.22  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.03/1.22  thf(d10_xboole_0, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.03/1.22  thf('27', plain,
% 1.03/1.22      (![X1 : $i, X3 : $i]:
% 1.03/1.22         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.03/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.22  thf('28', plain,
% 1.03/1.22      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.03/1.22  thf('29', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['23', '28'])).
% 1.03/1.22  thf(l13_xboole_0, axiom,
% 1.03/1.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.03/1.22  thf('30', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf('31', plain,
% 1.03/1.22      (![X46 : $i, X47 : $i]: (v1_funct_2 @ (sk_C @ X46 @ X47) @ X47 @ X46)),
% 1.03/1.22      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.03/1.22  thf('32', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf('33', plain,
% 1.03/1.22      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('34', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf(d1_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.22           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.22             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.22         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.22           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.22             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.22  thf(zf_stmt_1, axiom,
% 1.03/1.22    (![B:$i,A:$i]:
% 1.03/1.22     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.22       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.22  thf('35', plain,
% 1.03/1.22      (![X38 : $i, X39 : $i]:
% 1.03/1.22         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.22  thf('36', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.22  thf(zf_stmt_3, axiom,
% 1.03/1.22    (![C:$i,B:$i,A:$i]:
% 1.03/1.22     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.22       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.22  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.22  thf(zf_stmt_5, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.22         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.22           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.22             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.22  thf('37', plain,
% 1.03/1.22      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.03/1.22         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.03/1.22          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.03/1.22          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.22  thf('38', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.03/1.22        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.03/1.22      inference('sup-', [status(thm)], ['36', '37'])).
% 1.03/1.22  thf('39', plain,
% 1.03/1.22      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.03/1.22      inference('sup-', [status(thm)], ['35', '38'])).
% 1.03/1.22  thf('40', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('41', plain,
% 1.03/1.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.03/1.22         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.03/1.22          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.03/1.22          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.03/1.22  thf('42', plain,
% 1.03/1.22      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.03/1.22        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['40', '41'])).
% 1.03/1.22  thf('43', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.22  thf('44', plain,
% 1.03/1.22      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.03/1.22         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 1.03/1.22          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.22  thf('45', plain,
% 1.03/1.22      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['43', '44'])).
% 1.03/1.22  thf('46', plain,
% 1.03/1.22      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.03/1.22        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['42', '45'])).
% 1.03/1.22  thf('47', plain,
% 1.03/1.22      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['39', '46'])).
% 1.03/1.22  thf(t146_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( v1_relat_1 @ A ) =>
% 1.03/1.22       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.03/1.22  thf('48', plain,
% 1.03/1.22      (![X16 : $i]:
% 1.03/1.22         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 1.03/1.22          | ~ (v1_relat_1 @ X16))),
% 1.03/1.22      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.03/1.22  thf(t169_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( v1_relat_1 @ A ) =>
% 1.03/1.22       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.03/1.22  thf('49', plain,
% 1.03/1.22      (![X17 : $i]:
% 1.03/1.22         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 1.03/1.22          | ~ (v1_relat_1 @ X17))),
% 1.03/1.22      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.03/1.22  thf('50', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf(t154_funct_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.03/1.22       ( ( v2_funct_1 @ B ) =>
% 1.03/1.22         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.03/1.22  thf('51', plain,
% 1.03/1.22      (![X24 : $i, X25 : $i]:
% 1.03/1.22         (~ (v2_funct_1 @ X24)
% 1.03/1.22          | ((k9_relat_1 @ X24 @ X25)
% 1.03/1.22              = (k10_relat_1 @ (k2_funct_1 @ X24) @ X25))
% 1.03/1.22          | ~ (v1_funct_1 @ X24)
% 1.03/1.22          | ~ (v1_relat_1 @ X24))),
% 1.03/1.22      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.03/1.22  thf('52', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (((k9_relat_1 @ sk_C_1 @ X0)
% 1.03/1.22            = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))
% 1.03/1.22          | ~ (v1_relat_1 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ sk_C_1)
% 1.03/1.22          | ~ (v2_funct_1 @ sk_C_1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['50', '51'])).
% 1.03/1.22  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('55', plain, ((v2_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('56', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((k9_relat_1 @ sk_C_1 @ X0)
% 1.03/1.22           = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 1.03/1.22      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.03/1.22  thf('57', plain,
% 1.03/1.22      ((((k9_relat_1 @ sk_C_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22          = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['49', '56'])).
% 1.03/1.22  thf('58', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf('59', plain,
% 1.03/1.22      (![X21 : $i]:
% 1.03/1.22         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.03/1.22          | ~ (v1_funct_1 @ X21)
% 1.03/1.22          | ~ (v1_relat_1 @ X21))),
% 1.03/1.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.22  thf('60', plain,
% 1.03/1.22      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22        | ~ (v1_relat_1 @ sk_C_1)
% 1.03/1.22        | ~ (v1_funct_1 @ sk_C_1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['58', '59'])).
% 1.03/1.22  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('63', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.22  thf('64', plain,
% 1.03/1.22      (((k9_relat_1 @ sk_C_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22         = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['57', '63'])).
% 1.03/1.22  thf('65', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf(t55_funct_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.22       ( ( v2_funct_1 @ A ) =>
% 1.03/1.22         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.03/1.22           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.03/1.22  thf('66', plain,
% 1.03/1.22      (![X28 : $i]:
% 1.03/1.22         (~ (v2_funct_1 @ X28)
% 1.03/1.22          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 1.03/1.22          | ~ (v1_funct_1 @ X28)
% 1.03/1.22          | ~ (v1_relat_1 @ X28))),
% 1.03/1.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.22  thf('67', plain,
% 1.03/1.22      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22        | ~ (v1_relat_1 @ sk_C_1)
% 1.03/1.22        | ~ (v1_funct_1 @ sk_C_1)
% 1.03/1.22        | ~ (v2_funct_1 @ sk_C_1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['65', '66'])).
% 1.03/1.22  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('70', plain, ((v2_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('71', plain,
% 1.03/1.22      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.03/1.22  thf('72', plain,
% 1.03/1.22      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 1.03/1.22         = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['64', '71'])).
% 1.03/1.22  thf('73', plain,
% 1.03/1.22      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22        | ~ (v1_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['48', '72'])).
% 1.03/1.22  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf('75', plain,
% 1.03/1.22      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['73', '74'])).
% 1.03/1.22  thf('76', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.22  thf('77', plain,
% 1.03/1.22      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.03/1.22         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 1.03/1.22          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.22  thf('78', plain,
% 1.03/1.22      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['76', '77'])).
% 1.03/1.22  thf('79', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('80', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['78', '79'])).
% 1.03/1.22  thf('81', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['75', '80'])).
% 1.03/1.22  thf(t3_funct_2, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.22       ( ( v1_funct_1 @ A ) & 
% 1.03/1.22         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.03/1.22         ( m1_subset_1 @
% 1.03/1.22           A @ 
% 1.03/1.22           ( k1_zfmisc_1 @
% 1.03/1.22             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.03/1.22  thf('82', plain,
% 1.03/1.22      (![X48 : $i]:
% 1.03/1.22         ((v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))
% 1.03/1.22          | ~ (v1_funct_1 @ X48)
% 1.03/1.22          | ~ (v1_relat_1 @ X48))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.03/1.22  thf('83', plain,
% 1.03/1.22      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 1.03/1.22         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.03/1.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['81', '82'])).
% 1.03/1.22  thf('84', plain,
% 1.03/1.22      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.03/1.22  thf('85', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.22  thf('86', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf('87', plain,
% 1.03/1.22      (![X21 : $i]:
% 1.03/1.22         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.03/1.22          | ~ (v1_funct_1 @ X21)
% 1.03/1.22          | ~ (v1_relat_1 @ X21))),
% 1.03/1.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.22  thf('88', plain,
% 1.03/1.22      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22        | ~ (v1_relat_1 @ sk_C_1)
% 1.03/1.22        | ~ (v1_funct_1 @ sk_C_1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['86', '87'])).
% 1.03/1.22  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 1.03/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.22  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('91', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.03/1.22  thf('92', plain,
% 1.03/1.22      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['83', '84', '85', '91'])).
% 1.03/1.22  thf('93', plain,
% 1.03/1.22      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A)
% 1.03/1.22        | ((sk_B) = (k1_xboole_0)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['47', '92'])).
% 1.03/1.22  thf('94', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf('95', plain,
% 1.03/1.22      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('96', plain,
% 1.03/1.22      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['94', '95'])).
% 1.03/1.22  thf('97', plain,
% 1.03/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['93', '96'])).
% 1.03/1.22  thf('98', plain,
% 1.03/1.22      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('demod', [status(thm)], ['33', '34', '97'])).
% 1.03/1.22  thf('99', plain,
% 1.03/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['93', '96'])).
% 1.03/1.22  thf('100', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('101', plain,
% 1.03/1.22      (![X8 : $i, X9 : $i]:
% 1.03/1.22         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.03/1.22  thf('102', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.03/1.22      inference('sup-', [status(thm)], ['100', '101'])).
% 1.03/1.22  thf('103', plain,
% 1.03/1.22      (![X1 : $i, X3 : $i]:
% 1.03/1.22         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.03/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.22  thf('104', plain,
% 1.03/1.22      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 1.03/1.22        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['102', '103'])).
% 1.03/1.22  thf('105', plain,
% 1.03/1.22      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C_1)
% 1.03/1.22         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1))))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['99', '104'])).
% 1.03/1.22  thf('106', plain,
% 1.03/1.22      (![X5 : $i, X6 : $i]:
% 1.03/1.22         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.03/1.22  thf('107', plain,
% 1.03/1.22      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.22      inference('simplify', [status(thm)], ['106'])).
% 1.03/1.22  thf('108', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.03/1.22  thf('109', plain,
% 1.03/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['93', '96'])).
% 1.03/1.22  thf('110', plain,
% 1.03/1.22      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.22      inference('simplify', [status(thm)], ['106'])).
% 1.03/1.22  thf('111', plain,
% 1.03/1.22      ((((k1_xboole_0) = (sk_C_1)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('demod', [status(thm)], ['105', '107', '108', '109', '110'])).
% 1.03/1.22  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.03/1.22  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.22  thf(fc14_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( v1_xboole_0 @ A ) =>
% 1.03/1.22       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 1.03/1.22         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 1.03/1.22  thf('113', plain,
% 1.03/1.22      (![X15 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ (k4_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 1.03/1.22      inference('cnf', [status(esa)], [fc14_relat_1])).
% 1.03/1.22  thf('114', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf('115', plain,
% 1.03/1.22      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['113', '114'])).
% 1.03/1.22  thf('116', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['112', '115'])).
% 1.03/1.22  thf('117', plain,
% 1.03/1.22      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('demod', [status(thm)], ['98', '111', '116'])).
% 1.03/1.22  thf('118', plain,
% 1.03/1.22      ((![X0 : $i]:
% 1.03/1.22          (~ (v1_funct_2 @ X0 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['32', '117'])).
% 1.03/1.22  thf('119', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ (sk_C @ sk_A @ k1_xboole_0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['31', '118'])).
% 1.03/1.22  thf('120', plain,
% 1.03/1.22      ((![X0 : $i]:
% 1.03/1.22          (~ (v1_xboole_0 @ (sk_C @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['30', '119'])).
% 1.03/1.22  thf('121', plain,
% 1.03/1.22      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.03/1.22         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['29', '120'])).
% 1.03/1.22  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.22  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.22  thf('124', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 1.03/1.22      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.03/1.22  thf('125', plain,
% 1.03/1.22      (~
% 1.03/1.22       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.03/1.22       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 1.03/1.22       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('126', plain,
% 1.03/1.22      (~
% 1.03/1.22       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.22      inference('sat_resolution*', [status(thm)], ['17', '124', '125'])).
% 1.03/1.22  thf('127', plain,
% 1.03/1.22      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.03/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.03/1.22      inference('simpl_trail', [status(thm)], ['10', '126'])).
% 1.03/1.22  thf('128', plain,
% 1.03/1.22      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.03/1.22  thf('129', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf('130', plain,
% 1.03/1.22      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.03/1.22      inference('simplify', [status(thm)], ['18'])).
% 1.03/1.22  thf('131', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup+', [status(thm)], ['129', '130'])).
% 1.03/1.22  thf('132', plain,
% 1.03/1.22      (![X48 : $i]:
% 1.03/1.22         ((m1_subset_1 @ X48 @ 
% 1.03/1.22           (k1_zfmisc_1 @ 
% 1.03/1.22            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 1.03/1.22          | ~ (v1_funct_1 @ X48)
% 1.03/1.22          | ~ (v1_relat_1 @ X48))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.03/1.22  thf('133', plain,
% 1.03/1.22      (![X38 : $i, X39 : $i]:
% 1.03/1.22         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.22  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.22  thf('135', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.03/1.22      inference('sup+', [status(thm)], ['133', '134'])).
% 1.03/1.22  thf('136', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.03/1.22        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.03/1.22      inference('sup-', [status(thm)], ['36', '37'])).
% 1.03/1.22  thf('137', plain,
% 1.03/1.22      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.03/1.22      inference('sup-', [status(thm)], ['135', '136'])).
% 1.03/1.22  thf('138', plain,
% 1.03/1.22      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.03/1.22        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['42', '45'])).
% 1.03/1.22  thf('139', plain,
% 1.03/1.22      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['137', '138'])).
% 1.03/1.22  thf('140', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf('141', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.03/1.22  thf('142', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup+', [status(thm)], ['129', '130'])).
% 1.03/1.22  thf('143', plain,
% 1.03/1.22      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('split', [status(esa)], ['0'])).
% 1.03/1.22  thf('144', plain,
% 1.03/1.22      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.03/1.22         | ~ (v1_xboole_0 @ sk_B)))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['142', '143'])).
% 1.03/1.22  thf('145', plain,
% 1.03/1.22      (((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.03/1.22         | ~ (v1_xboole_0 @ sk_B)))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['141', '144'])).
% 1.03/1.22  thf('146', plain,
% 1.03/1.22      ((![X0 : $i]:
% 1.03/1.22          (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ X0))
% 1.03/1.22           | ~ (v1_xboole_0 @ X0)
% 1.03/1.22           | ~ (v1_xboole_0 @ sk_B)))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['140', '145'])).
% 1.03/1.22  thf('147', plain,
% 1.03/1.22      ((![X0 : $i]:
% 1.03/1.22          (((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.03/1.22           | ~ (v1_xboole_0 @ X0)
% 1.03/1.22           | ~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ X0))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['139', '146'])).
% 1.03/1.22  thf('148', plain,
% 1.03/1.22      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22         | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22         | ~ (v1_xboole_0 @ 
% 1.03/1.22              (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ 
% 1.03/1.22               (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))
% 1.03/1.22         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['132', '147'])).
% 1.03/1.22  thf('149', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.22  thf('150', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.03/1.22  thf('151', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['75', '80'])).
% 1.03/1.22  thf('152', plain,
% 1.03/1.22      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.03/1.22  thf('153', plain,
% 1.03/1.22      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1)))
% 1.03/1.22         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('demod', [status(thm)], ['148', '149', '150', '151', '152'])).
% 1.03/1.22  thf('154', plain,
% 1.03/1.22      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.03/1.22         | ~ (v1_xboole_0 @ sk_B)
% 1.03/1.22         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['131', '153'])).
% 1.03/1.22  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.22  thf('156', plain,
% 1.03/1.22      (((~ (v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('demod', [status(thm)], ['154', '155'])).
% 1.03/1.22  thf('157', plain,
% 1.03/1.22      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['137', '138'])).
% 1.03/1.22  thf('158', plain,
% 1.03/1.22      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 1.03/1.22         <= (~
% 1.03/1.22             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.22      inference('clc', [status(thm)], ['156', '157'])).
% 1.03/1.22  thf('159', plain,
% 1.03/1.22      (~
% 1.03/1.22       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.03/1.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.22      inference('sat_resolution*', [status(thm)], ['17', '124', '125'])).
% 1.03/1.22  thf('160', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 1.03/1.22  thf('161', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['128', '160'])).
% 1.03/1.22  thf('162', plain,
% 1.03/1.22      (![X48 : $i]:
% 1.03/1.22         ((m1_subset_1 @ X48 @ 
% 1.03/1.22           (k1_zfmisc_1 @ 
% 1.03/1.22            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 1.03/1.22          | ~ (v1_funct_1 @ X48)
% 1.03/1.22          | ~ (v1_relat_1 @ X48))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.03/1.22  thf('163', plain,
% 1.03/1.22      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.03/1.22         (k1_zfmisc_1 @ 
% 1.03/1.22          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 1.03/1.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.03/1.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['161', '162'])).
% 1.03/1.22  thf('164', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.03/1.22      inference('demod', [status(thm)], ['75', '80'])).
% 1.03/1.22  thf('165', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.22  thf('166', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.03/1.22  thf('167', plain,
% 1.03/1.22      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.03/1.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.03/1.22      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 1.03/1.22  thf('168', plain, ($false), inference('demod', [status(thm)], ['127', '167'])).
% 1.03/1.22  
% 1.03/1.22  % SZS output end Refutation
% 1.03/1.22  
% 1.07/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
