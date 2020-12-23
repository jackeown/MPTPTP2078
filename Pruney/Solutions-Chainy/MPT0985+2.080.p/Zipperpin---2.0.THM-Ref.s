%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e6xTFeDgQO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:37 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  257 (4781 expanded)
%              Number of leaves         :   43 (1455 expanded)
%              Depth                    :   36
%              Number of atoms          : 2025 (72898 expanded)
%              Number of equality atoms :  118 (2869 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
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

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['32','33'])).

thf('59',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X43: $i] :
      ( ( v1_funct_2 @ X43 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('65',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','78'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('92',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('95',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','92','93','94'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('97',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','92','93','94'])).

thf('99',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('100',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('102',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('104',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('105',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('114',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('116',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('117',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('118',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['112','114','115','116','117'])).

thf('119',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','118'])).

thf('120',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('121',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','92','93','94'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['119','122','125'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('127',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('128',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('131',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('132',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','121'])).

thf('136',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','140'])).

thf('142',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('146',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('148',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['144','150'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['96','126','151'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('154',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','152','153'])).

thf('155',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','154'])).

thf('156',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('157',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('158',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('160',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['156','164'])).

thf('166',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('167',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('171',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('173',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('178',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['169','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X2 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['168','182'])).

thf('184',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['183'])).

thf('185',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('186',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('188',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ( X42 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('192',plain,(
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('194',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('195',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','140'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['190','200'])).

thf('202',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['190','200'])).

thf('203',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 = X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( X1 = X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['204'])).

thf('206',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','152','153'])).

thf('207',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['165','207','208','209','210'])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['155','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e6xTFeDgQO
% 0.16/0.37  % Computer   : n009.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 12:31:41 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.62/1.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.62/1.79  % Solved by: fo/fo7.sh
% 1.62/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.62/1.79  % done 2322 iterations in 1.304s
% 1.62/1.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.62/1.79  % SZS output start Refutation
% 1.62/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.62/1.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.62/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.62/1.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.62/1.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.62/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.62/1.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.62/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.62/1.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.62/1.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.62/1.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.62/1.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.62/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.62/1.79  thf(sk_C_type, type, sk_C: $i).
% 1.62/1.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.62/1.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.62/1.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.62/1.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.62/1.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.62/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.62/1.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.62/1.79  thf(t31_funct_2, conjecture,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.79       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.62/1.79         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.62/1.79           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.62/1.79           ( m1_subset_1 @
% 1.62/1.79             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.62/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.62/1.79    (~( ![A:$i,B:$i,C:$i]:
% 1.62/1.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.79          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.62/1.79            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.62/1.79              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.62/1.79              ( m1_subset_1 @
% 1.62/1.79                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.62/1.79    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.62/1.79  thf('0', plain,
% 1.62/1.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.62/1.79        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('1', plain,
% 1.62/1.79      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.62/1.79         <= (~
% 1.62/1.79             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.79      inference('split', [status(esa)], ['0'])).
% 1.62/1.79  thf('2', plain,
% 1.62/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(cc1_relset_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.79       ( v1_relat_1 @ C ) ))).
% 1.62/1.79  thf('3', plain,
% 1.62/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.62/1.79         ((v1_relat_1 @ X20)
% 1.62/1.79          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.62/1.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.62/1.79  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf(dt_k2_funct_1, axiom,
% 1.62/1.79    (![A:$i]:
% 1.62/1.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.62/1.79       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.62/1.79         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.62/1.79  thf('5', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('6', plain,
% 1.62/1.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.62/1.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('split', [status(esa)], ['0'])).
% 1.62/1.79  thf('7', plain,
% 1.62/1.79      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.62/1.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['5', '6'])).
% 1.62/1.79  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('9', plain,
% 1.62/1.79      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('demod', [status(thm)], ['7', '8'])).
% 1.62/1.79  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['4', '9'])).
% 1.62/1.79  thf('11', plain,
% 1.62/1.79      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('split', [status(esa)], ['0'])).
% 1.62/1.79  thf(d1_funct_2, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.62/1.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.62/1.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.62/1.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.62/1.79  thf(zf_stmt_1, axiom,
% 1.62/1.79    (![B:$i,A:$i]:
% 1.62/1.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.79       ( zip_tseitin_0 @ B @ A ) ))).
% 1.62/1.79  thf('12', plain,
% 1.62/1.79      (![X35 : $i, X36 : $i]:
% 1.62/1.79         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.79  thf('13', plain,
% 1.62/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.62/1.79  thf(zf_stmt_3, axiom,
% 1.62/1.79    (![C:$i,B:$i,A:$i]:
% 1.62/1.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.62/1.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.62/1.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.62/1.79  thf(zf_stmt_5, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.62/1.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.62/1.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.62/1.79  thf('14', plain,
% 1.62/1.79      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.62/1.79         (~ (zip_tseitin_0 @ X40 @ X41)
% 1.62/1.79          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 1.62/1.79          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.62/1.79  thf('15', plain,
% 1.62/1.79      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.62/1.79      inference('sup-', [status(thm)], ['13', '14'])).
% 1.62/1.79  thf('16', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.62/1.79      inference('sup-', [status(thm)], ['12', '15'])).
% 1.62/1.79  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('18', plain,
% 1.62/1.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.62/1.79         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 1.62/1.79          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 1.62/1.79          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.62/1.79  thf('19', plain,
% 1.62/1.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.62/1.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['17', '18'])).
% 1.62/1.79  thf('20', plain,
% 1.62/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(redefinition_k1_relset_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.62/1.79  thf('21', plain,
% 1.62/1.79      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.62/1.79         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.62/1.79          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.62/1.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.62/1.79  thf('22', plain,
% 1.62/1.79      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.62/1.79      inference('sup-', [status(thm)], ['20', '21'])).
% 1.62/1.79  thf('23', plain,
% 1.62/1.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.62/1.79      inference('demod', [status(thm)], ['19', '22'])).
% 1.62/1.79  thf('24', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['16', '23'])).
% 1.62/1.79  thf(t55_funct_1, axiom,
% 1.62/1.79    (![A:$i]:
% 1.62/1.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.62/1.79       ( ( v2_funct_1 @ A ) =>
% 1.62/1.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.62/1.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.62/1.79  thf('25', plain,
% 1.62/1.79      (![X19 : $i]:
% 1.62/1.79         (~ (v2_funct_1 @ X19)
% 1.62/1.79          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 1.62/1.79          | ~ (v1_funct_1 @ X19)
% 1.62/1.79          | ~ (v1_relat_1 @ X19))),
% 1.62/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.62/1.79  thf('26', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('27', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('28', plain,
% 1.62/1.79      (![X19 : $i]:
% 1.62/1.79         (~ (v2_funct_1 @ X19)
% 1.62/1.79          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 1.62/1.79          | ~ (v1_funct_1 @ X19)
% 1.62/1.79          | ~ (v1_relat_1 @ X19))),
% 1.62/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.62/1.79  thf('29', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('30', plain,
% 1.62/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(redefinition_k2_relset_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.62/1.79  thf('31', plain,
% 1.62/1.79      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.62/1.79         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.62/1.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.62/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.62/1.79  thf('32', plain,
% 1.62/1.79      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.62/1.79      inference('sup-', [status(thm)], ['30', '31'])).
% 1.62/1.79  thf('33', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('34', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.62/1.79      inference('sup+', [status(thm)], ['32', '33'])).
% 1.62/1.79  thf('35', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('36', plain,
% 1.62/1.79      (![X19 : $i]:
% 1.62/1.79         (~ (v2_funct_1 @ X19)
% 1.62/1.79          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 1.62/1.79          | ~ (v1_funct_1 @ X19)
% 1.62/1.79          | ~ (v1_relat_1 @ X19))),
% 1.62/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.62/1.79  thf(d10_xboole_0, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.62/1.79  thf('37', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.62/1.79      inference('simplify', [status(thm)], ['37'])).
% 1.62/1.79  thf(d18_relat_1, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( v1_relat_1 @ B ) =>
% 1.62/1.79       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.62/1.79  thf('39', plain,
% 1.62/1.79      (![X14 : $i, X15 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.62/1.79          | (v4_relat_1 @ X14 @ X15)
% 1.62/1.79          | ~ (v1_relat_1 @ X14))),
% 1.62/1.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.62/1.79  thf('40', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['38', '39'])).
% 1.62/1.79  thf('41', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.62/1.79          | ~ (v1_relat_1 @ X0)
% 1.62/1.79          | ~ (v1_funct_1 @ X0)
% 1.62/1.79          | ~ (v2_funct_1 @ X0)
% 1.62/1.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['36', '40'])).
% 1.62/1.79  thf('42', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (v1_relat_1 @ X0)
% 1.62/1.79          | ~ (v1_funct_1 @ X0)
% 1.62/1.79          | ~ (v2_funct_1 @ X0)
% 1.62/1.79          | ~ (v1_funct_1 @ X0)
% 1.62/1.79          | ~ (v1_relat_1 @ X0)
% 1.62/1.79          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['35', '41'])).
% 1.62/1.79  thf('43', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.62/1.79          | ~ (v2_funct_1 @ X0)
% 1.62/1.79          | ~ (v1_funct_1 @ X0)
% 1.62/1.79          | ~ (v1_relat_1 @ X0))),
% 1.62/1.79      inference('simplify', [status(thm)], ['42'])).
% 1.62/1.79  thf('44', plain,
% 1.62/1.79      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.62/1.79        | ~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.79      inference('sup+', [status(thm)], ['34', '43'])).
% 1.62/1.79  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('48', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.62/1.79      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.62/1.79  thf('49', plain,
% 1.62/1.79      (![X14 : $i, X15 : $i]:
% 1.62/1.79         (~ (v4_relat_1 @ X14 @ X15)
% 1.62/1.79          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.62/1.79          | ~ (v1_relat_1 @ X14))),
% 1.62/1.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.62/1.79  thf('50', plain,
% 1.62/1.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.79        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.62/1.79      inference('sup-', [status(thm)], ['48', '49'])).
% 1.62/1.79  thf('51', plain,
% 1.62/1.79      ((~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.62/1.79      inference('sup-', [status(thm)], ['29', '50'])).
% 1.62/1.79  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.62/1.79      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.62/1.79  thf('55', plain,
% 1.62/1.79      (![X0 : $i, X2 : $i]:
% 1.62/1.79         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('56', plain,
% 1.62/1.79      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.62/1.79        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['54', '55'])).
% 1.62/1.79  thf('57', plain,
% 1.62/1.79      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.62/1.79        | ~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | ~ (v2_funct_1 @ sk_C)
% 1.62/1.79        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['28', '56'])).
% 1.62/1.79  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.62/1.79      inference('sup+', [status(thm)], ['32', '33'])).
% 1.62/1.79  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.62/1.79      inference('simplify', [status(thm)], ['37'])).
% 1.62/1.79  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('63', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.79      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 1.62/1.79  thf(t3_funct_2, axiom,
% 1.62/1.79    (![A:$i]:
% 1.62/1.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.62/1.79       ( ( v1_funct_1 @ A ) & 
% 1.62/1.79         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.62/1.79         ( m1_subset_1 @
% 1.62/1.79           A @ 
% 1.62/1.79           ( k1_zfmisc_1 @
% 1.62/1.79             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.62/1.79  thf('64', plain,
% 1.62/1.79      (![X43 : $i]:
% 1.62/1.79         ((v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))
% 1.62/1.79          | ~ (v1_funct_1 @ X43)
% 1.62/1.79          | ~ (v1_relat_1 @ X43))),
% 1.62/1.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.62/1.79  thf('65', plain,
% 1.62/1.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.62/1.79         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.62/1.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['63', '64'])).
% 1.62/1.79  thf('66', plain,
% 1.62/1.79      ((~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.62/1.79           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['27', '65'])).
% 1.62/1.79  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('69', plain,
% 1.62/1.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.62/1.79           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.62/1.79  thf('70', plain,
% 1.62/1.79      ((~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.62/1.79           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['26', '69'])).
% 1.62/1.79  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('73', plain,
% 1.62/1.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.62/1.79        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.79      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.62/1.79  thf('74', plain,
% 1.62/1.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 1.62/1.79        | ~ (v1_relat_1 @ sk_C)
% 1.62/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.79        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.79      inference('sup+', [status(thm)], ['25', '73'])).
% 1.62/1.79  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('78', plain,
% 1.62/1.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.62/1.79      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.62/1.79  thf('79', plain,
% 1.62/1.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.62/1.79        | ((sk_B) = (k1_xboole_0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['24', '78'])).
% 1.62/1.79  thf('80', plain,
% 1.62/1.79      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('split', [status(esa)], ['0'])).
% 1.62/1.79  thf('81', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['79', '80'])).
% 1.62/1.79  thf('82', plain,
% 1.62/1.79      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['11', '81'])).
% 1.62/1.79  thf('83', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['79', '80'])).
% 1.62/1.79  thf('84', plain,
% 1.62/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(t3_subset, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.62/1.79  thf('85', plain,
% 1.62/1.79      (![X8 : $i, X9 : $i]:
% 1.62/1.79         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t3_subset])).
% 1.62/1.79  thf('86', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.62/1.79      inference('sup-', [status(thm)], ['84', '85'])).
% 1.62/1.79  thf('87', plain,
% 1.62/1.79      (![X0 : $i, X2 : $i]:
% 1.62/1.79         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('88', plain,
% 1.62/1.79      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 1.62/1.79        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['86', '87'])).
% 1.62/1.79  thf('89', plain,
% 1.62/1.79      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 1.62/1.79         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['83', '88'])).
% 1.62/1.79  thf(t113_zfmisc_1, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.62/1.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.62/1.79  thf('90', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i]:
% 1.62/1.79         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.62/1.79  thf('91', plain,
% 1.62/1.79      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.79      inference('simplify', [status(thm)], ['90'])).
% 1.62/1.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.62/1.79  thf('92', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.62/1.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.62/1.79  thf('93', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['79', '80'])).
% 1.62/1.79  thf('94', plain,
% 1.62/1.79      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.79      inference('simplify', [status(thm)], ['90'])).
% 1.62/1.79  thf('95', plain,
% 1.62/1.79      ((((k1_xboole_0) = (sk_C)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 1.62/1.79  thf('96', plain,
% 1.62/1.79      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['82', '95'])).
% 1.62/1.79  thf('97', plain,
% 1.62/1.79      (![X18 : $i]:
% 1.62/1.79         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.79          | ~ (v1_funct_1 @ X18)
% 1.62/1.79          | ~ (v1_relat_1 @ X18))),
% 1.62/1.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.79  thf('98', plain,
% 1.62/1.79      ((((k1_xboole_0) = (sk_C)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 1.62/1.79  thf('99', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.79      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 1.62/1.79  thf('100', plain,
% 1.62/1.79      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['98', '99'])).
% 1.62/1.79  thf('101', plain,
% 1.62/1.79      ((((sk_B) = (k1_xboole_0)))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['79', '80'])).
% 1.62/1.79  thf('102', plain,
% 1.62/1.79      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['100', '101'])).
% 1.62/1.79  thf('103', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.62/1.79      inference('simplify', [status(thm)], ['37'])).
% 1.62/1.79  thf('104', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.62/1.79      inference('simplify', [status(thm)], ['37'])).
% 1.62/1.79  thf(t11_relset_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( v1_relat_1 @ C ) =>
% 1.62/1.79       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.62/1.79           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.62/1.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.62/1.79  thf('105', plain,
% 1.62/1.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 1.62/1.79          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 1.62/1.79          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.62/1.79          | ~ (v1_relat_1 @ X32))),
% 1.62/1.79      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.62/1.79  thf('106', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]:
% 1.62/1.79         (~ (v1_relat_1 @ X0)
% 1.62/1.79          | (m1_subset_1 @ X0 @ 
% 1.62/1.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.62/1.79          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.62/1.79      inference('sup-', [status(thm)], ['104', '105'])).
% 1.62/1.79  thf('107', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((m1_subset_1 @ X0 @ 
% 1.62/1.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.62/1.79          | ~ (v1_relat_1 @ X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['103', '106'])).
% 1.62/1.79  thf('108', plain,
% 1.62/1.79      (![X8 : $i, X9 : $i]:
% 1.62/1.79         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t3_subset])).
% 1.62/1.79  thf('109', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (v1_relat_1 @ X0)
% 1.62/1.79          | (r1_tarski @ X0 @ 
% 1.62/1.79             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['107', '108'])).
% 1.62/1.79  thf('110', plain,
% 1.62/1.79      (![X0 : $i, X2 : $i]:
% 1.62/1.79         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('111', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (v1_relat_1 @ X0)
% 1.62/1.79          | ~ (r1_tarski @ 
% 1.62/1.79               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 1.62/1.79          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['109', '110'])).
% 1.62/1.79  thf('112', plain,
% 1.62/1.79      (((~ (r1_tarski @ 
% 1.62/1.79            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 1.62/1.79             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))) @ 
% 1.62/1.79            (k2_funct_1 @ k1_xboole_0))
% 1.62/1.79         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 1.62/1.79             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 1.62/1.79             = (k2_funct_1 @ k1_xboole_0))
% 1.62/1.79         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['102', '111'])).
% 1.62/1.79  thf('113', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i]:
% 1.62/1.79         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.62/1.79  thf('114', plain,
% 1.62/1.79      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.62/1.79      inference('simplify', [status(thm)], ['113'])).
% 1.62/1.79  thf('115', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.62/1.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.62/1.79  thf('116', plain,
% 1.62/1.79      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['100', '101'])).
% 1.62/1.79  thf('117', plain,
% 1.62/1.79      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.62/1.79      inference('simplify', [status(thm)], ['113'])).
% 1.62/1.79  thf('118', plain,
% 1.62/1.79      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 1.62/1.79         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['112', '114', '115', '116', '117'])).
% 1.62/1.80  thf('119', plain,
% 1.62/1.80      (((~ (v1_relat_1 @ k1_xboole_0)
% 1.62/1.80         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.62/1.80         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 1.62/1.80         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['97', '118'])).
% 1.62/1.80  thf('120', plain,
% 1.62/1.80      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.62/1.80      inference('simplify', [status(thm)], ['113'])).
% 1.62/1.80  thf(fc6_relat_1, axiom,
% 1.62/1.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.62/1.80  thf('121', plain,
% 1.62/1.80      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 1.62/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.62/1.80  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.62/1.80      inference('sup+', [status(thm)], ['120', '121'])).
% 1.62/1.80  thf('123', plain,
% 1.62/1.80      ((((k1_xboole_0) = (sk_C)))
% 1.62/1.80         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.80      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 1.62/1.80  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('125', plain,
% 1.62/1.80      (((v1_funct_1 @ k1_xboole_0))
% 1.62/1.80         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.80      inference('sup+', [status(thm)], ['123', '124'])).
% 1.62/1.80  thf('126', plain,
% 1.62/1.80      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 1.62/1.80         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.62/1.80      inference('demod', [status(thm)], ['119', '122', '125'])).
% 1.62/1.80  thf(t4_subset_1, axiom,
% 1.62/1.80    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.62/1.80  thf('127', plain,
% 1.62/1.80      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.62/1.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.62/1.80  thf('128', plain,
% 1.62/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.62/1.80         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.62/1.80          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.62/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.62/1.80  thf('129', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['127', '128'])).
% 1.62/1.80  thf('130', plain,
% 1.62/1.80      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.62/1.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.62/1.80  thf(cc2_relset_1, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.62/1.80  thf('131', plain,
% 1.62/1.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.62/1.80         ((v4_relat_1 @ X23 @ X24)
% 1.62/1.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.62/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.62/1.80  thf('132', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.62/1.80      inference('sup-', [status(thm)], ['130', '131'])).
% 1.62/1.80  thf('133', plain,
% 1.62/1.80      (![X14 : $i, X15 : $i]:
% 1.62/1.80         (~ (v4_relat_1 @ X14 @ X15)
% 1.62/1.80          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.62/1.80          | ~ (v1_relat_1 @ X14))),
% 1.62/1.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.62/1.80  thf('134', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         (~ (v1_relat_1 @ k1_xboole_0)
% 1.62/1.80          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['132', '133'])).
% 1.62/1.80  thf('135', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.62/1.80      inference('sup+', [status(thm)], ['120', '121'])).
% 1.62/1.80  thf('136', plain,
% 1.62/1.80      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.62/1.80      inference('demod', [status(thm)], ['134', '135'])).
% 1.62/1.80  thf('137', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.62/1.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.62/1.80  thf('138', plain,
% 1.62/1.80      (![X0 : $i, X2 : $i]:
% 1.62/1.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.62/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.80  thf('139', plain,
% 1.62/1.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['137', '138'])).
% 1.62/1.80  thf('140', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['136', '139'])).
% 1.62/1.80  thf('141', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('demod', [status(thm)], ['129', '140'])).
% 1.62/1.80  thf('142', plain,
% 1.62/1.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.62/1.80         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 1.62/1.80          | (v1_funct_2 @ X39 @ X37 @ X38)
% 1.62/1.80          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.62/1.80  thf('143', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         (((X1) != (k1_xboole_0))
% 1.62/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.62/1.80          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['141', '142'])).
% 1.62/1.80  thf('144', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.62/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.62/1.80      inference('simplify', [status(thm)], ['143'])).
% 1.62/1.80  thf('145', plain,
% 1.62/1.80      (![X35 : $i, X36 : $i]:
% 1.62/1.80         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.80  thf('146', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 1.62/1.80      inference('simplify', [status(thm)], ['145'])).
% 1.62/1.80  thf('147', plain,
% 1.62/1.80      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.62/1.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.62/1.80  thf('148', plain,
% 1.62/1.80      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.62/1.80         (~ (zip_tseitin_0 @ X40 @ X41)
% 1.62/1.80          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 1.62/1.80          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.62/1.80  thf('149', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.62/1.80      inference('sup-', [status(thm)], ['147', '148'])).
% 1.62/1.80  thf('150', plain,
% 1.62/1.80      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.62/1.80      inference('sup-', [status(thm)], ['146', '149'])).
% 1.62/1.80  thf('151', plain,
% 1.62/1.80      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.62/1.80      inference('demod', [status(thm)], ['144', '150'])).
% 1.62/1.80  thf('152', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.62/1.80      inference('demod', [status(thm)], ['96', '126', '151'])).
% 1.62/1.80  thf('153', plain,
% 1.62/1.80      (~
% 1.62/1.80       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.62/1.80       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.62/1.80       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('split', [status(esa)], ['0'])).
% 1.62/1.80  thf('154', plain,
% 1.62/1.80      (~
% 1.62/1.80       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.62/1.80      inference('sat_resolution*', [status(thm)], ['10', '152', '153'])).
% 1.62/1.80  thf('155', plain,
% 1.62/1.80      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.62/1.80      inference('simpl_trail', [status(thm)], ['1', '154'])).
% 1.62/1.80  thf('156', plain,
% 1.62/1.80      (![X19 : $i]:
% 1.62/1.80         (~ (v2_funct_1 @ X19)
% 1.62/1.80          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 1.62/1.80          | ~ (v1_funct_1 @ X19)
% 1.62/1.80          | ~ (v1_relat_1 @ X19))),
% 1.62/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.62/1.80  thf('157', plain,
% 1.62/1.80      (![X18 : $i]:
% 1.62/1.80         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.80          | ~ (v1_funct_1 @ X18)
% 1.62/1.80          | ~ (v1_relat_1 @ X18))),
% 1.62/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.80  thf('158', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 1.62/1.80  thf('159', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         ((m1_subset_1 @ X0 @ 
% 1.62/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.62/1.80          | ~ (v1_relat_1 @ X0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['103', '106'])).
% 1.62/1.80  thf('160', plain,
% 1.62/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ 
% 1.62/1.80          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.62/1.80        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('sup+', [status(thm)], ['158', '159'])).
% 1.62/1.80  thf('161', plain,
% 1.62/1.80      ((~ (v1_relat_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ 
% 1.62/1.80            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['157', '160'])).
% 1.62/1.80  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.80  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('164', plain,
% 1.62/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.62/1.80      inference('demod', [status(thm)], ['161', '162', '163'])).
% 1.62/1.80  thf('165', plain,
% 1.62/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 1.62/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.80      inference('sup+', [status(thm)], ['156', '164'])).
% 1.62/1.80  thf('166', plain,
% 1.62/1.80      (![X35 : $i, X36 : $i]:
% 1.62/1.80         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.80  thf('167', plain,
% 1.62/1.80      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.62/1.80      inference('simplify', [status(thm)], ['113'])).
% 1.62/1.80  thf('168', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.80         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.62/1.80      inference('sup+', [status(thm)], ['166', '167'])).
% 1.62/1.80  thf('169', plain,
% 1.62/1.80      (![X18 : $i]:
% 1.62/1.80         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.62/1.80          | ~ (v1_funct_1 @ X18)
% 1.62/1.80          | ~ (v1_relat_1 @ X18))),
% 1.62/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.62/1.80  thf('170', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         ((m1_subset_1 @ X0 @ 
% 1.62/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.62/1.80          | ~ (v1_relat_1 @ X0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['103', '106'])).
% 1.62/1.80  thf('171', plain,
% 1.62/1.80      (![X35 : $i, X36 : $i]:
% 1.62/1.80         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.80  thf('172', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.80         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.62/1.80      inference('sup+', [status(thm)], ['166', '167'])).
% 1.62/1.80  thf('173', plain,
% 1.62/1.80      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('split', [status(esa)], ['0'])).
% 1.62/1.80  thf('174', plain,
% 1.62/1.80      ((![X0 : $i]:
% 1.62/1.80          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['172', '173'])).
% 1.62/1.80  thf('175', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.80          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 1.62/1.80           | (zip_tseitin_0 @ X0 @ X2)
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['171', '174'])).
% 1.62/1.80  thf('176', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X0)
% 1.62/1.80           | (zip_tseitin_0 @ 
% 1.62/1.80              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.62/1.80               (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.62/1.80              X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['170', '175'])).
% 1.62/1.80  thf('177', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 1.62/1.80  thf('178', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X0)
% 1.62/1.80           | (zip_tseitin_0 @ 
% 1.62/1.80              (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('demod', [status(thm)], ['176', '177'])).
% 1.62/1.80  thf('179', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          (~ (v1_relat_1 @ sk_C)
% 1.62/1.80           | ~ (v1_funct_1 @ sk_C)
% 1.62/1.80           | (zip_tseitin_0 @ 
% 1.62/1.80              (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ X0)
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['169', '178'])).
% 1.62/1.80  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.80  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('182', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          ((zip_tseitin_0 @ 
% 1.62/1.80            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ X0)
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('demod', [status(thm)], ['179', '180', '181'])).
% 1.62/1.80  thf('183', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.80          ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X2)
% 1.62/1.80           | (zip_tseitin_0 @ sk_B @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup+', [status(thm)], ['168', '182'])).
% 1.62/1.80  thf('184', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_B @ X1)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('condensation', [status(thm)], ['183'])).
% 1.62/1.80  thf('185', plain,
% 1.62/1.80      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.62/1.80      inference('sup-', [status(thm)], ['13', '14'])).
% 1.62/1.80  thf('186', plain,
% 1.62/1.80      ((![X0 : $i]:
% 1.62/1.80          ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 1.62/1.80           | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['184', '185'])).
% 1.62/1.80  thf('187', plain,
% 1.62/1.80      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['19', '22'])).
% 1.62/1.80  thf('188', plain,
% 1.62/1.80      ((![X0 : $i]:
% 1.62/1.80          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['186', '187'])).
% 1.62/1.80  thf('189', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.62/1.80      inference('sup-', [status(thm)], ['147', '148'])).
% 1.62/1.80  thf('190', plain,
% 1.62/1.80      ((![X0 : $i]:
% 1.62/1.80          (((sk_A) = (k1_relat_1 @ sk_C))
% 1.62/1.80           | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['188', '189'])).
% 1.62/1.80  thf('191', plain,
% 1.62/1.80      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.62/1.80         (((X40) != (k1_xboole_0))
% 1.62/1.80          | ((X41) = (k1_xboole_0))
% 1.62/1.80          | (v1_funct_2 @ X42 @ X41 @ X40)
% 1.62/1.80          | ((X42) != (k1_xboole_0))
% 1.62/1.80          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.62/1.80  thf('192', plain,
% 1.62/1.80      (![X41 : $i]:
% 1.62/1.80         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.62/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ k1_xboole_0)))
% 1.62/1.80          | (v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 1.62/1.80          | ((X41) = (k1_xboole_0)))),
% 1.62/1.80      inference('simplify', [status(thm)], ['191'])).
% 1.62/1.80  thf('193', plain,
% 1.62/1.80      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('simplify', [status(thm)], ['90'])).
% 1.62/1.80  thf('194', plain,
% 1.62/1.80      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.62/1.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.62/1.80  thf('195', plain,
% 1.62/1.80      (![X41 : $i]:
% 1.62/1.80         ((v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 1.62/1.80          | ((X41) = (k1_xboole_0)))),
% 1.62/1.80      inference('demod', [status(thm)], ['192', '193', '194'])).
% 1.62/1.80  thf('196', plain,
% 1.62/1.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.62/1.80         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 1.62/1.80          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 1.62/1.80          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.62/1.80  thf('197', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         (((X0) = (k1_xboole_0))
% 1.62/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.62/1.80          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['195', '196'])).
% 1.62/1.80  thf('198', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]:
% 1.62/1.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('demod', [status(thm)], ['129', '140'])).
% 1.62/1.80  thf('199', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         (((X0) = (k1_xboole_0))
% 1.62/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.62/1.80          | ((X0) = (k1_xboole_0)))),
% 1.62/1.80      inference('demod', [status(thm)], ['197', '198'])).
% 1.62/1.80  thf('200', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.62/1.80          | ((X0) = (k1_xboole_0)))),
% 1.62/1.80      inference('simplify', [status(thm)], ['199'])).
% 1.62/1.80  thf('201', plain,
% 1.62/1.80      ((![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X0) = (k1_xboole_0))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['190', '200'])).
% 1.62/1.80  thf('202', plain,
% 1.62/1.80      ((![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X0) = (k1_xboole_0))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['190', '200'])).
% 1.62/1.80  thf('203', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]:
% 1.62/1.80          (((X1) = (X0))
% 1.62/1.80           | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.62/1.80           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('sup+', [status(thm)], ['201', '202'])).
% 1.62/1.80  thf('204', plain,
% 1.62/1.80      ((![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X1) = (X0))))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('simplify', [status(thm)], ['203'])).
% 1.62/1.80  thf('205', plain,
% 1.62/1.80      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.62/1.80      inference('condensation', [status(thm)], ['204'])).
% 1.62/1.80  thf('206', plain,
% 1.62/1.80      (~
% 1.62/1.80       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.62/1.80      inference('sat_resolution*', [status(thm)], ['10', '152', '153'])).
% 1.62/1.80  thf('207', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.62/1.80      inference('simpl_trail', [status(thm)], ['205', '206'])).
% 1.62/1.80  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.80  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('211', plain,
% 1.62/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.62/1.80      inference('demod', [status(thm)], ['165', '207', '208', '209', '210'])).
% 1.62/1.80  thf('212', plain, ($false), inference('demod', [status(thm)], ['155', '211'])).
% 1.62/1.80  
% 1.62/1.80  % SZS output end Refutation
% 1.62/1.80  
% 1.62/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
