%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F0L0kw8xxI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:46 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  219 (2329 expanded)
%              Number of leaves         :   40 ( 708 expanded)
%              Depth                    :   32
%              Number of atoms          : 1786 (34434 expanded)
%              Number of equality atoms :   72 (1179 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('19',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['34','39','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('59',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','72'])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('78',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('86',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('87',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('90',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['85','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','106'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('110',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('115',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('118',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['108','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','136'])).

thf('138',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('139',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','137','138'])).

thf('140',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['76','139'])).

thf('141',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('143',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('144',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56'])).

thf('146',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['141','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('149',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','137','138'])).

thf('151',plain,
    ( ( k1_relset_1 @ k1_xboole_0 @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('155',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('156',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C )
        = sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('162',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['160','163'])).

thf('165',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','75'])).

thf('166',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('168',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('169',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('172',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','137','138'])).

thf('174',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','174'])).

thf('176',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['140','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F0L0kw8xxI
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.31/3.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.31/3.54  % Solved by: fo/fo7.sh
% 3.31/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.31/3.54  % done 3401 iterations in 3.084s
% 3.31/3.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.31/3.54  % SZS output start Refutation
% 3.31/3.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.31/3.54  thf(sk_C_type, type, sk_C: $i).
% 3.31/3.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.31/3.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.31/3.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.31/3.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.31/3.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.31/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.31/3.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.31/3.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.31/3.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.31/3.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.31/3.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.31/3.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.31/3.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.31/3.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.31/3.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.31/3.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.31/3.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.31/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.31/3.54  thf(sk_B_type, type, sk_B: $i).
% 3.31/3.54  thf(t31_funct_2, conjecture,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.31/3.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.54       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.31/3.54         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.31/3.54           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.31/3.54           ( m1_subset_1 @
% 3.31/3.54             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.31/3.54  thf(zf_stmt_0, negated_conjecture,
% 3.31/3.54    (~( ![A:$i,B:$i,C:$i]:
% 3.31/3.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.31/3.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.54          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.31/3.54            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.31/3.54              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.31/3.54              ( m1_subset_1 @
% 3.31/3.54                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.31/3.54    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.31/3.54  thf('0', plain,
% 3.31/3.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.31/3.54        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.31/3.54        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('1', plain,
% 3.31/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf(d1_funct_2, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.31/3.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.31/3.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.31/3.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.31/3.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.31/3.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.31/3.54  thf(zf_stmt_1, axiom,
% 3.31/3.54    (![B:$i,A:$i]:
% 3.31/3.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.31/3.54       ( zip_tseitin_0 @ B @ A ) ))).
% 3.31/3.54  thf('2', plain,
% 3.31/3.54      (![X36 : $i, X37 : $i]:
% 3.31/3.54         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.31/3.54  thf('3', plain,
% 3.31/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.31/3.54  thf(zf_stmt_3, axiom,
% 3.31/3.54    (![C:$i,B:$i,A:$i]:
% 3.31/3.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.31/3.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.31/3.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.31/3.54  thf(zf_stmt_5, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.31/3.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.31/3.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.31/3.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.31/3.54  thf('4', plain,
% 3.31/3.54      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.31/3.54         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.31/3.54          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.31/3.54          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.31/3.54  thf('5', plain,
% 3.31/3.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.31/3.54      inference('sup-', [status(thm)], ['3', '4'])).
% 3.31/3.54  thf('6', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 3.31/3.54      inference('sup-', [status(thm)], ['2', '5'])).
% 3.31/3.54  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('8', plain,
% 3.31/3.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.31/3.54         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 3.31/3.54          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 3.31/3.54          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.31/3.54  thf('9', plain,
% 3.31/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 3.31/3.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['7', '8'])).
% 3.31/3.54  thf('10', plain,
% 3.31/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf(redefinition_k1_relset_1, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.31/3.54  thf('11', plain,
% 3.31/3.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.31/3.54         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.31/3.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.31/3.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.31/3.54  thf('12', plain,
% 3.31/3.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.31/3.54      inference('sup-', [status(thm)], ['10', '11'])).
% 3.31/3.54  thf('13', plain,
% 3.31/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.31/3.54      inference('demod', [status(thm)], ['9', '12'])).
% 3.31/3.54  thf('14', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['6', '13'])).
% 3.31/3.54  thf(t55_funct_1, axiom,
% 3.31/3.54    (![A:$i]:
% 3.31/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.31/3.54       ( ( v2_funct_1 @ A ) =>
% 3.31/3.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.31/3.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.31/3.54  thf('15', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf(dt_k2_funct_1, axiom,
% 3.31/3.54    (![A:$i]:
% 3.31/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.31/3.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.31/3.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.31/3.54  thf('16', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('17', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('18', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf('19', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('20', plain,
% 3.31/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf(redefinition_k2_relset_1, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.31/3.54  thf('21', plain,
% 3.31/3.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.31/3.54         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 3.31/3.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 3.31/3.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.31/3.54  thf('22', plain,
% 3.31/3.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.31/3.54      inference('sup-', [status(thm)], ['20', '21'])).
% 3.31/3.54  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('24', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.31/3.54      inference('sup+', [status(thm)], ['22', '23'])).
% 3.31/3.54  thf('25', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('26', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf(d10_xboole_0, axiom,
% 3.31/3.54    (![A:$i,B:$i]:
% 3.31/3.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.31/3.54  thf('27', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.31/3.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.31/3.54  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.31/3.54      inference('simplify', [status(thm)], ['27'])).
% 3.31/3.54  thf(d18_relat_1, axiom,
% 3.31/3.54    (![A:$i,B:$i]:
% 3.31/3.54     ( ( v1_relat_1 @ B ) =>
% 3.31/3.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.31/3.54  thf('29', plain,
% 3.31/3.54      (![X16 : $i, X17 : $i]:
% 3.31/3.54         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.31/3.54          | (v4_relat_1 @ X16 @ X17)
% 3.31/3.54          | ~ (v1_relat_1 @ X16))),
% 3.31/3.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.31/3.54  thf('30', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['28', '29'])).
% 3.31/3.54  thf('31', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['26', '30'])).
% 3.31/3.54  thf('32', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['25', '31'])).
% 3.31/3.54  thf('33', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('simplify', [status(thm)], ['32'])).
% 3.31/3.54  thf('34', plain,
% 3.31/3.54      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 3.31/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.31/3.54      inference('sup+', [status(thm)], ['24', '33'])).
% 3.31/3.54  thf('35', plain,
% 3.31/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf(cc2_relat_1, axiom,
% 3.31/3.54    (![A:$i]:
% 3.31/3.54     ( ( v1_relat_1 @ A ) =>
% 3.31/3.54       ( ![B:$i]:
% 3.31/3.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.31/3.54  thf('36', plain,
% 3.31/3.54      (![X14 : $i, X15 : $i]:
% 3.31/3.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.31/3.54          | (v1_relat_1 @ X14)
% 3.31/3.54          | ~ (v1_relat_1 @ X15))),
% 3.31/3.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.31/3.54  thf('37', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.31/3.54      inference('sup-', [status(thm)], ['35', '36'])).
% 3.31/3.54  thf(fc6_relat_1, axiom,
% 3.31/3.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.31/3.54  thf('38', plain,
% 3.31/3.54      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 3.31/3.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.31/3.54  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('42', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 3.31/3.54      inference('demod', [status(thm)], ['34', '39', '40', '41'])).
% 3.31/3.54  thf('43', plain,
% 3.31/3.54      (![X16 : $i, X17 : $i]:
% 3.31/3.54         (~ (v4_relat_1 @ X16 @ X17)
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.31/3.54          | ~ (v1_relat_1 @ X16))),
% 3.31/3.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.31/3.54  thf('44', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.31/3.54        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 3.31/3.54      inference('sup-', [status(thm)], ['42', '43'])).
% 3.31/3.54  thf('45', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 3.31/3.54      inference('sup-', [status(thm)], ['19', '44'])).
% 3.31/3.54  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 3.31/3.54      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.31/3.54  thf('49', plain,
% 3.31/3.54      (![X0 : $i, X2 : $i]:
% 3.31/3.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.31/3.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.31/3.54  thf('50', plain,
% 3.31/3.54      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.31/3.54        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['48', '49'])).
% 3.31/3.54  thf('51', plain,
% 3.31/3.54      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 3.31/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v2_funct_1 @ sk_C)
% 3.31/3.54        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['18', '50'])).
% 3.31/3.54  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.31/3.54      inference('sup+', [status(thm)], ['22', '23'])).
% 3.31/3.54  thf('53', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.31/3.54      inference('simplify', [status(thm)], ['27'])).
% 3.31/3.54  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('57', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('demod', [status(thm)], ['51', '52', '53', '54', '55', '56'])).
% 3.31/3.54  thf(t3_funct_2, axiom,
% 3.31/3.54    (![A:$i]:
% 3.31/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.31/3.54       ( ( v1_funct_1 @ A ) & 
% 3.31/3.54         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.31/3.54         ( m1_subset_1 @
% 3.31/3.54           A @ 
% 3.31/3.54           ( k1_zfmisc_1 @
% 3.31/3.54             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.31/3.54  thf('58', plain,
% 3.31/3.54      (![X44 : $i]:
% 3.31/3.54         ((v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))
% 3.31/3.54          | ~ (v1_funct_1 @ X44)
% 3.31/3.54          | ~ (v1_relat_1 @ X44))),
% 3.31/3.54      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.31/3.54  thf('59', plain,
% 3.31/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.31/3.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.31/3.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.31/3.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['57', '58'])).
% 3.31/3.54  thf('60', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.31/3.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.31/3.54           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['17', '59'])).
% 3.31/3.54  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('63', plain,
% 3.31/3.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.31/3.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.31/3.54           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 3.31/3.54  thf('64', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.31/3.54           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['16', '63'])).
% 3.31/3.54  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('67', plain,
% 3.31/3.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.31/3.54        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.31/3.54  thf('68', plain,
% 3.31/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 3.31/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.31/3.54      inference('sup+', [status(thm)], ['15', '67'])).
% 3.31/3.54  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('72', plain,
% 3.31/3.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 3.31/3.54      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 3.31/3.54  thf('73', plain,
% 3.31/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.31/3.54        | ((sk_B) = (k1_xboole_0)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['14', '72'])).
% 3.31/3.54  thf('74', plain,
% 3.31/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf('75', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.31/3.54  thf('76', plain,
% 3.31/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['1', '75'])).
% 3.31/3.54  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('78', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('79', plain,
% 3.31/3.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.31/3.54         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf('80', plain,
% 3.31/3.54      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 3.31/3.54         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['78', '79'])).
% 3.31/3.54  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('82', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.31/3.54      inference('demod', [status(thm)], ['80', '81'])).
% 3.31/3.54  thf('83', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['77', '82'])).
% 3.31/3.54  thf('84', plain,
% 3.31/3.54      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf('85', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['6', '13'])).
% 3.31/3.54  thf('86', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf('87', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('88', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf('89', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.31/3.54      inference('simplify', [status(thm)], ['27'])).
% 3.31/3.54  thf('90', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.31/3.54      inference('simplify', [status(thm)], ['27'])).
% 3.31/3.54  thf(t11_relset_1, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( v1_relat_1 @ C ) =>
% 3.31/3.54       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 3.31/3.54           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 3.31/3.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.31/3.54  thf('91', plain,
% 3.31/3.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.31/3.54         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 3.31/3.54          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 3.31/3.54          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.31/3.54          | ~ (v1_relat_1 @ X33))),
% 3.31/3.54      inference('cnf', [status(esa)], [t11_relset_1])).
% 3.31/3.54  thf('92', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | (m1_subset_1 @ X0 @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 3.31/3.54          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 3.31/3.54      inference('sup-', [status(thm)], ['90', '91'])).
% 3.31/3.54  thf('93', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((m1_subset_1 @ X0 @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('sup-', [status(thm)], ['89', '92'])).
% 3.31/3.54  thf('94', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54           (k1_zfmisc_1 @ 
% 3.31/3.54            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['88', '93'])).
% 3.31/3.54  thf('95', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ 
% 3.31/3.54              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 3.31/3.54               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['87', '94'])).
% 3.31/3.54  thf('96', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54           (k1_zfmisc_1 @ 
% 3.31/3.54            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('simplify', [status(thm)], ['95'])).
% 3.31/3.54  thf('97', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0))),
% 3.31/3.54      inference('sup+', [status(thm)], ['86', '96'])).
% 3.31/3.54  thf('98', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ 
% 3.31/3.54              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 3.31/3.54      inference('simplify', [status(thm)], ['97'])).
% 3.31/3.54  thf('99', plain,
% 3.31/3.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 3.31/3.54        | ((sk_B) = (k1_xboole_0))
% 3.31/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.31/3.54      inference('sup+', [status(thm)], ['85', '98'])).
% 3.31/3.54  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.31/3.54      inference('sup+', [status(thm)], ['22', '23'])).
% 3.31/3.54  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('104', plain,
% 3.31/3.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.31/3.54        | ((sk_B) = (k1_xboole_0)))),
% 3.31/3.54      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 3.31/3.54  thf('105', plain,
% 3.31/3.54      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf('106', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['104', '105'])).
% 3.31/3.54  thf('107', plain,
% 3.31/3.54      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('demod', [status(thm)], ['84', '106'])).
% 3.31/3.54  thf('108', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['104', '105'])).
% 3.31/3.54  thf('109', plain,
% 3.31/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf(cc2_relset_1, axiom,
% 3.31/3.54    (![A:$i,B:$i,C:$i]:
% 3.31/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.31/3.54  thf('110', plain,
% 3.31/3.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.31/3.54         ((v4_relat_1 @ X24 @ X25)
% 3.31/3.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.31/3.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.31/3.54  thf('111', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 3.31/3.54      inference('sup-', [status(thm)], ['109', '110'])).
% 3.31/3.54  thf('112', plain,
% 3.31/3.54      (![X16 : $i, X17 : $i]:
% 3.31/3.54         (~ (v4_relat_1 @ X16 @ X17)
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.31/3.54          | ~ (v1_relat_1 @ X16))),
% 3.31/3.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.31/3.54  thf('113', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 3.31/3.54      inference('sup-', [status(thm)], ['111', '112'])).
% 3.31/3.54  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('115', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 3.31/3.54      inference('demod', [status(thm)], ['113', '114'])).
% 3.31/3.54  thf('116', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('117', plain,
% 3.31/3.54      (![X23 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X23)
% 3.31/3.54          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 3.31/3.54          | ~ (v1_funct_1 @ X23)
% 3.31/3.54          | ~ (v1_relat_1 @ X23))),
% 3.31/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.31/3.54  thf('118', plain,
% 3.31/3.54      (![X22 : $i]:
% 3.31/3.54         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 3.31/3.54          | ~ (v1_funct_1 @ X22)
% 3.31/3.54          | ~ (v1_relat_1 @ X22))),
% 3.31/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.31/3.54  thf('119', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('simplify', [status(thm)], ['32'])).
% 3.31/3.54  thf('120', plain,
% 3.31/3.54      (![X16 : $i, X17 : $i]:
% 3.31/3.54         (~ (v4_relat_1 @ X16 @ X17)
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.31/3.54          | ~ (v1_relat_1 @ X16))),
% 3.31/3.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.31/3.54  thf('121', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['119', '120'])).
% 3.31/3.54  thf('122', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('sup-', [status(thm)], ['118', '121'])).
% 3.31/3.54  thf('123', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (~ (v2_funct_1 @ X0)
% 3.31/3.54          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('simplify', [status(thm)], ['122'])).
% 3.31/3.54  thf('124', plain,
% 3.31/3.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.31/3.54         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 3.31/3.54          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 3.31/3.54          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.31/3.54          | ~ (v1_relat_1 @ X33))),
% 3.31/3.54      inference('cnf', [status(esa)], [t11_relset_1])).
% 3.31/3.54  thf('125', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1)))
% 3.31/3.54          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 3.31/3.54      inference('sup-', [status(thm)], ['123', '124'])).
% 3.31/3.54  thf('126', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1)))
% 3.31/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('sup-', [status(thm)], ['117', '125'])).
% 3.31/3.54  thf('127', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1)))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 3.31/3.54      inference('simplify', [status(thm)], ['126'])).
% 3.31/3.54  thf('128', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         (~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.31/3.54          | ~ (v1_relat_1 @ X0)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['116', '127'])).
% 3.31/3.54  thf('129', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i]:
% 3.31/3.54         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1)))
% 3.31/3.54          | ~ (v2_funct_1 @ X0)
% 3.31/3.54          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.31/3.54          | ~ (v1_funct_1 @ X0)
% 3.31/3.54          | ~ (v1_relat_1 @ X0))),
% 3.31/3.54      inference('simplify', [status(thm)], ['128'])).
% 3.31/3.54  thf('130', plain,
% 3.31/3.54      ((~ (v1_relat_1 @ sk_C)
% 3.31/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.31/3.54        | ~ (v2_funct_1 @ sk_C)
% 3.31/3.54        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A))))),
% 3.31/3.54      inference('sup-', [status(thm)], ['115', '129'])).
% 3.31/3.54  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 3.31/3.54      inference('demod', [status(thm)], ['37', '38'])).
% 3.31/3.54  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.54  thf('134', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.31/3.54      inference('sup+', [status(thm)], ['22', '23'])).
% 3.31/3.54  thf('135', plain,
% 3.31/3.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 3.31/3.54  thf('136', plain,
% 3.31/3.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 3.31/3.54         <= (~
% 3.31/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.31/3.54      inference('sup+', [status(thm)], ['108', '135'])).
% 3.31/3.54  thf('137', plain,
% 3.31/3.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.31/3.54      inference('demod', [status(thm)], ['107', '136'])).
% 3.31/3.54  thf('138', plain,
% 3.31/3.54      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 3.31/3.54       ~
% 3.31/3.54       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 3.31/3.54       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('split', [status(esa)], ['0'])).
% 3.31/3.54  thf('139', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.31/3.54      inference('sat_resolution*', [status(thm)], ['83', '137', '138'])).
% 3.31/3.54  thf('140', plain,
% 3.31/3.54      (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A)),
% 3.31/3.54      inference('simpl_trail', [status(thm)], ['76', '139'])).
% 3.31/3.54  thf('141', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.31/3.54  thf('142', plain,
% 3.31/3.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 3.31/3.54  thf('143', plain,
% 3.31/3.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.31/3.54         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.31/3.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.31/3.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.31/3.54  thf('144', plain,
% 3.31/3.54      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 3.31/3.54         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['142', '143'])).
% 3.31/3.54  thf('145', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.31/3.54      inference('demod', [status(thm)], ['51', '52', '53', '54', '55', '56'])).
% 3.31/3.54  thf('146', plain,
% 3.31/3.54      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 3.31/3.54      inference('demod', [status(thm)], ['144', '145'])).
% 3.31/3.54  thf('147', plain,
% 3.31/3.54      ((((k1_relset_1 @ k1_xboole_0 @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_B)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['141', '146'])).
% 3.31/3.54  thf('148', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.31/3.54  thf('149', plain,
% 3.31/3.54      ((((k1_relset_1 @ k1_xboole_0 @ sk_A @ (k2_funct_1 @ sk_C))
% 3.31/3.54          = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['147', '148'])).
% 3.31/3.54  thf('150', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.31/3.54      inference('sat_resolution*', [status(thm)], ['83', '137', '138'])).
% 3.31/3.54  thf('151', plain,
% 3.31/3.54      (((k1_relset_1 @ k1_xboole_0 @ sk_A @ (k2_funct_1 @ sk_C))
% 3.31/3.54         = (k1_xboole_0))),
% 3.31/3.54      inference('simpl_trail', [status(thm)], ['149', '150'])).
% 3.31/3.54  thf('152', plain,
% 3.31/3.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.31/3.54         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 3.31/3.54          | (v1_funct_2 @ X40 @ X38 @ X39)
% 3.31/3.54          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.31/3.54  thf('153', plain,
% 3.31/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.31/3.54        | ~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ k1_xboole_0)
% 3.31/3.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))),
% 3.31/3.54      inference('sup-', [status(thm)], ['151', '152'])).
% 3.31/3.54  thf('154', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 3.31/3.54      inference('demod', [status(thm)], ['113', '114'])).
% 3.31/3.54  thf('155', plain,
% 3.31/3.54      (![X36 : $i, X37 : $i]:
% 3.31/3.54         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.31/3.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.31/3.54  thf('156', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 3.31/3.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.31/3.54  thf('157', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.31/3.54         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.31/3.54      inference('sup+', [status(thm)], ['155', '156'])).
% 3.31/3.54  thf('158', plain,
% 3.31/3.54      (![X0 : $i, X2 : $i]:
% 3.31/3.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.31/3.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.31/3.54  thf('159', plain,
% 3.31/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.31/3.54         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['157', '158'])).
% 3.31/3.54  thf('160', plain,
% 3.31/3.54      (![X0 : $i]:
% 3.31/3.54         (((k1_relat_1 @ sk_C) = (sk_A)) | (zip_tseitin_0 @ sk_A @ X0))),
% 3.31/3.54      inference('sup-', [status(thm)], ['154', '159'])).
% 3.31/3.54  thf('161', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.31/3.54  thf('162', plain,
% 3.31/3.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 3.31/3.54      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 3.31/3.54  thf('163', plain,
% 3.31/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['161', '162'])).
% 3.31/3.54  thf('164', plain,
% 3.31/3.54      ((![X0 : $i]:
% 3.31/3.54          ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A)
% 3.31/3.54           | (zip_tseitin_0 @ sk_A @ X0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup+', [status(thm)], ['160', '163'])).
% 3.31/3.54  thf('165', plain,
% 3.31/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['1', '75'])).
% 3.31/3.54  thf('166', plain,
% 3.31/3.54      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('clc', [status(thm)], ['164', '165'])).
% 3.31/3.54  thf('167', plain,
% 3.31/3.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.31/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 3.31/3.54  thf('168', plain,
% 3.31/3.54      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.31/3.54         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.31/3.54          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.31/3.54          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.31/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.31/3.54  thf('169', plain,
% 3.31/3.54      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 3.31/3.54        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 3.31/3.54      inference('sup-', [status(thm)], ['167', '168'])).
% 3.31/3.54  thf('170', plain,
% 3.31/3.54      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['166', '169'])).
% 3.31/3.54  thf('171', plain,
% 3.31/3.54      ((((sk_B) = (k1_xboole_0)))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('sup-', [status(thm)], ['73', '74'])).
% 3.31/3.54  thf('172', plain,
% 3.31/3.54      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ k1_xboole_0))
% 3.31/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.31/3.54      inference('demod', [status(thm)], ['170', '171'])).
% 3.31/3.54  thf('173', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.31/3.54      inference('sat_resolution*', [status(thm)], ['83', '137', '138'])).
% 3.31/3.54  thf('174', plain,
% 3.31/3.54      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ k1_xboole_0)),
% 3.31/3.54      inference('simpl_trail', [status(thm)], ['172', '173'])).
% 3.31/3.54  thf('175', plain,
% 3.31/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.31/3.54        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))),
% 3.31/3.54      inference('demod', [status(thm)], ['153', '174'])).
% 3.31/3.54  thf('176', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A)),
% 3.31/3.54      inference('simplify', [status(thm)], ['175'])).
% 3.31/3.54  thf('177', plain, ($false), inference('demod', [status(thm)], ['140', '176'])).
% 3.31/3.54  
% 3.31/3.54  % SZS output end Refutation
% 3.31/3.54  
% 3.41/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
