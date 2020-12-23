%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.23CpIHvIM1

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:37 EST 2020

% Result     : Theorem 12.96s
% Output     : Refutation 12.96s
% Verified   : 
% Statistics : Number of formulae       :  245 (4066 expanded)
%              Number of leaves         :   41 (1243 expanded)
%              Depth                    :   49
%              Number of atoms          : 1801 (62623 expanded)
%              Number of equality atoms :   97 (2373 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
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
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','92','93','94'])).

thf('100',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('101',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('103',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('105',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('107',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','108'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('110',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('111',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','92','93','94'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['109','112','115'])).

thf('117',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','116'])).

thf('118',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('119',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('122',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','125'])).

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
    inference('sup-',[status(thm)],['110','111'])).

thf('136',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('138',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','138'])).

thf('140',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('144',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('146',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['142','148'])).

thf('150',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['96','126','149'])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','150','151'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','152'])).

thf('154',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('158',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('159',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['154','167'])).

thf('169',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('170',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('171',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('172',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('177',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','152'])).

thf('182',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['175','182'])).

thf('184',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['170','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['169','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('195',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('197',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','197','198','199','200'])).

thf('202',plain,(
    $false ),
    inference(demod,[status(thm)],['153','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.23CpIHvIM1
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.96/13.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.96/13.17  % Solved by: fo/fo7.sh
% 12.96/13.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.96/13.17  % done 8783 iterations in 12.714s
% 12.96/13.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.96/13.17  % SZS output start Refutation
% 12.96/13.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.96/13.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.96/13.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.96/13.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.96/13.17  thf(sk_B_type, type, sk_B: $i).
% 12.96/13.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.96/13.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.96/13.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.96/13.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.96/13.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.96/13.17  thf(sk_C_type, type, sk_C: $i).
% 12.96/13.17  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 12.96/13.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.96/13.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.96/13.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.96/13.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.96/13.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.96/13.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.96/13.18  thf(sk_A_type, type, sk_A: $i).
% 12.96/13.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.96/13.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.96/13.18  thf(t31_funct_2, conjecture,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.96/13.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.96/13.18       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.96/13.18         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.96/13.18           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.96/13.18           ( m1_subset_1 @
% 12.96/13.18             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 12.96/13.18  thf(zf_stmt_0, negated_conjecture,
% 12.96/13.18    (~( ![A:$i,B:$i,C:$i]:
% 12.96/13.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.96/13.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.96/13.18          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.96/13.18            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.96/13.18              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.96/13.18              ( m1_subset_1 @
% 12.96/13.18                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 12.96/13.18    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 12.96/13.18  thf('0', plain,
% 12.96/13.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.96/13.18        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('1', plain,
% 12.96/13.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.96/13.18         <= (~
% 12.96/13.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.96/13.18      inference('split', [status(esa)], ['0'])).
% 12.96/13.18  thf('2', plain,
% 12.96/13.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf(cc1_relset_1, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( v1_relat_1 @ C ) ))).
% 12.96/13.18  thf('3', plain,
% 12.96/13.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 12.96/13.18         ((v1_relat_1 @ X20)
% 12.96/13.18          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 12.96/13.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.96/13.18  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf(dt_k2_funct_1, axiom,
% 12.96/13.18    (![A:$i]:
% 12.96/13.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.96/13.18       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 12.96/13.18         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 12.96/13.18  thf('5', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('6', plain,
% 12.96/13.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 12.96/13.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('split', [status(esa)], ['0'])).
% 12.96/13.18  thf('7', plain,
% 12.96/13.18      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 12.96/13.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['5', '6'])).
% 12.96/13.18  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('9', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('demod', [status(thm)], ['7', '8'])).
% 12.96/13.18  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['4', '9'])).
% 12.96/13.18  thf('11', plain,
% 12.96/13.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('split', [status(esa)], ['0'])).
% 12.96/13.18  thf(d1_funct_2, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.96/13.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.96/13.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.96/13.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.96/13.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.96/13.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.96/13.18  thf(zf_stmt_1, axiom,
% 12.96/13.18    (![B:$i,A:$i]:
% 12.96/13.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.96/13.18       ( zip_tseitin_0 @ B @ A ) ))).
% 12.96/13.18  thf('12', plain,
% 12.96/13.18      (![X32 : $i, X33 : $i]:
% 12.96/13.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.96/13.18  thf('13', plain,
% 12.96/13.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.96/13.18  thf(zf_stmt_3, axiom,
% 12.96/13.18    (![C:$i,B:$i,A:$i]:
% 12.96/13.18     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.96/13.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.96/13.18  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 12.96/13.18  thf(zf_stmt_5, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.96/13.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.96/13.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.96/13.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.96/13.18  thf('14', plain,
% 12.96/13.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 12.96/13.18         (~ (zip_tseitin_0 @ X37 @ X38)
% 12.96/13.18          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 12.96/13.18          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.96/13.18  thf('15', plain,
% 12.96/13.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['13', '14'])).
% 12.96/13.18  thf('16', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['12', '15'])).
% 12.96/13.18  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('18', plain,
% 12.96/13.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.96/13.18         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 12.96/13.18          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 12.96/13.18          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.96/13.18  thf('19', plain,
% 12.96/13.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 12.96/13.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['17', '18'])).
% 12.96/13.18  thf('20', plain,
% 12.96/13.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf(redefinition_k1_relset_1, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.96/13.18  thf('21', plain,
% 12.96/13.18      (![X26 : $i, X27 : $i, X28 : $i]:
% 12.96/13.18         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 12.96/13.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 12.96/13.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.96/13.18  thf('22', plain,
% 12.96/13.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 12.96/13.18      inference('sup-', [status(thm)], ['20', '21'])).
% 12.96/13.18  thf('23', plain,
% 12.96/13.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['19', '22'])).
% 12.96/13.18  thf('24', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['16', '23'])).
% 12.96/13.18  thf(t55_funct_1, axiom,
% 12.96/13.18    (![A:$i]:
% 12.96/13.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.96/13.18       ( ( v2_funct_1 @ A ) =>
% 12.96/13.18         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 12.96/13.18           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 12.96/13.18  thf('25', plain,
% 12.96/13.18      (![X19 : $i]:
% 12.96/13.18         (~ (v2_funct_1 @ X19)
% 12.96/13.18          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 12.96/13.18          | ~ (v1_funct_1 @ X19)
% 12.96/13.18          | ~ (v1_relat_1 @ X19))),
% 12.96/13.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.96/13.18  thf('26', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('27', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('28', plain,
% 12.96/13.18      (![X19 : $i]:
% 12.96/13.18         (~ (v2_funct_1 @ X19)
% 12.96/13.18          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 12.96/13.18          | ~ (v1_funct_1 @ X19)
% 12.96/13.18          | ~ (v1_relat_1 @ X19))),
% 12.96/13.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.96/13.18  thf('29', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('30', plain,
% 12.96/13.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf(redefinition_k2_relset_1, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 12.96/13.18  thf('31', plain,
% 12.96/13.18      (![X29 : $i, X30 : $i, X31 : $i]:
% 12.96/13.18         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 12.96/13.18          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 12.96/13.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 12.96/13.18  thf('32', plain,
% 12.96/13.18      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 12.96/13.18      inference('sup-', [status(thm)], ['30', '31'])).
% 12.96/13.18  thf('33', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('34', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.96/13.18      inference('sup+', [status(thm)], ['32', '33'])).
% 12.96/13.18  thf('35', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('36', plain,
% 12.96/13.18      (![X19 : $i]:
% 12.96/13.18         (~ (v2_funct_1 @ X19)
% 12.96/13.18          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 12.96/13.18          | ~ (v1_funct_1 @ X19)
% 12.96/13.18          | ~ (v1_relat_1 @ X19))),
% 12.96/13.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.96/13.18  thf(d10_xboole_0, axiom,
% 12.96/13.18    (![A:$i,B:$i]:
% 12.96/13.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.96/13.18  thf('37', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 12.96/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.96/13.18  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.96/13.18      inference('simplify', [status(thm)], ['37'])).
% 12.96/13.18  thf(d18_relat_1, axiom,
% 12.96/13.18    (![A:$i,B:$i]:
% 12.96/13.18     ( ( v1_relat_1 @ B ) =>
% 12.96/13.18       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 12.96/13.18  thf('39', plain,
% 12.96/13.18      (![X14 : $i, X15 : $i]:
% 12.96/13.18         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 12.96/13.18          | (v4_relat_1 @ X14 @ X15)
% 12.96/13.18          | ~ (v1_relat_1 @ X14))),
% 12.96/13.18      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.96/13.18  thf('40', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['38', '39'])).
% 12.96/13.18  thf('41', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 12.96/13.18          | ~ (v1_relat_1 @ X0)
% 12.96/13.18          | ~ (v1_funct_1 @ X0)
% 12.96/13.18          | ~ (v2_funct_1 @ X0)
% 12.96/13.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['36', '40'])).
% 12.96/13.18  thf('42', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_relat_1 @ X0)
% 12.96/13.18          | ~ (v1_funct_1 @ X0)
% 12.96/13.18          | ~ (v2_funct_1 @ X0)
% 12.96/13.18          | ~ (v1_funct_1 @ X0)
% 12.96/13.18          | ~ (v1_relat_1 @ X0)
% 12.96/13.18          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['35', '41'])).
% 12.96/13.18  thf('43', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 12.96/13.18          | ~ (v2_funct_1 @ X0)
% 12.96/13.18          | ~ (v1_funct_1 @ X0)
% 12.96/13.18          | ~ (v1_relat_1 @ X0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['42'])).
% 12.96/13.18  thf('44', plain,
% 12.96/13.18      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 12.96/13.18        | ~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v2_funct_1 @ sk_C))),
% 12.96/13.18      inference('sup+', [status(thm)], ['34', '43'])).
% 12.96/13.18  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('48', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 12.96/13.18      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 12.96/13.18  thf('49', plain,
% 12.96/13.18      (![X14 : $i, X15 : $i]:
% 12.96/13.18         (~ (v4_relat_1 @ X14 @ X15)
% 12.96/13.18          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 12.96/13.18          | ~ (v1_relat_1 @ X14))),
% 12.96/13.18      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.96/13.18  thf('50', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 12.96/13.18      inference('sup-', [status(thm)], ['48', '49'])).
% 12.96/13.18  thf('51', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 12.96/13.18      inference('sup-', [status(thm)], ['29', '50'])).
% 12.96/13.18  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 12.96/13.18      inference('demod', [status(thm)], ['51', '52', '53'])).
% 12.96/13.18  thf('55', plain,
% 12.96/13.18      (![X0 : $i, X2 : $i]:
% 12.96/13.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.96/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.96/13.18  thf('56', plain,
% 12.96/13.18      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 12.96/13.18        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['54', '55'])).
% 12.96/13.18  thf('57', plain,
% 12.96/13.18      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 12.96/13.18        | ~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v2_funct_1 @ sk_C)
% 12.96/13.18        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['28', '56'])).
% 12.96/13.18  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.96/13.18      inference('sup+', [status(thm)], ['32', '33'])).
% 12.96/13.18  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.96/13.18      inference('simplify', [status(thm)], ['37'])).
% 12.96/13.18  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('63', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 12.96/13.18  thf(t3_funct_2, axiom,
% 12.96/13.18    (![A:$i]:
% 12.96/13.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.96/13.18       ( ( v1_funct_1 @ A ) & 
% 12.96/13.18         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 12.96/13.18         ( m1_subset_1 @
% 12.96/13.18           A @ 
% 12.96/13.18           ( k1_zfmisc_1 @
% 12.96/13.18             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 12.96/13.18  thf('64', plain,
% 12.96/13.18      (![X43 : $i]:
% 12.96/13.18         ((v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))
% 12.96/13.18          | ~ (v1_funct_1 @ X43)
% 12.96/13.18          | ~ (v1_relat_1 @ X43))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 12.96/13.18  thf('65', plain,
% 12.96/13.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 12.96/13.18         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 12.96/13.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['63', '64'])).
% 12.96/13.18  thf('66', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 12.96/13.18           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['27', '65'])).
% 12.96/13.18  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('69', plain,
% 12.96/13.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 12.96/13.18           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('demod', [status(thm)], ['66', '67', '68'])).
% 12.96/13.18  thf('70', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 12.96/13.18           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['26', '69'])).
% 12.96/13.18  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('73', plain,
% 12.96/13.18      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 12.96/13.18        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['70', '71', '72'])).
% 12.96/13.18  thf('74', plain,
% 12.96/13.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 12.96/13.18        | ~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v2_funct_1 @ sk_C))),
% 12.96/13.18      inference('sup+', [status(thm)], ['25', '73'])).
% 12.96/13.18  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('78', plain,
% 12.96/13.18      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 12.96/13.18      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 12.96/13.18  thf('79', plain,
% 12.96/13.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.96/13.18        | ((sk_B) = (k1_xboole_0)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['24', '78'])).
% 12.96/13.18  thf('80', plain,
% 12.96/13.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('split', [status(esa)], ['0'])).
% 12.96/13.18  thf('81', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['79', '80'])).
% 12.96/13.18  thf('82', plain,
% 12.96/13.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['11', '81'])).
% 12.96/13.18  thf('83', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['79', '80'])).
% 12.96/13.18  thf('84', plain,
% 12.96/13.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf(t3_subset, axiom,
% 12.96/13.18    (![A:$i,B:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.96/13.18  thf('85', plain,
% 12.96/13.18      (![X8 : $i, X9 : $i]:
% 12.96/13.18         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_subset])).
% 12.96/13.18  thf('86', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 12.96/13.18      inference('sup-', [status(thm)], ['84', '85'])).
% 12.96/13.18  thf('87', plain,
% 12.96/13.18      (![X0 : $i, X2 : $i]:
% 12.96/13.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.96/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.96/13.18  thf('88', plain,
% 12.96/13.18      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 12.96/13.18        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['86', '87'])).
% 12.96/13.18  thf('89', plain,
% 12.96/13.18      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 12.96/13.18         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['83', '88'])).
% 12.96/13.18  thf(t113_zfmisc_1, axiom,
% 12.96/13.18    (![A:$i,B:$i]:
% 12.96/13.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 12.96/13.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 12.96/13.18  thf('90', plain,
% 12.96/13.18      (![X5 : $i, X6 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 12.96/13.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 12.96/13.18  thf('91', plain,
% 12.96/13.18      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['90'])).
% 12.96/13.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 12.96/13.18  thf('92', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.96/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.96/13.18  thf('93', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['79', '80'])).
% 12.96/13.18  thf('94', plain,
% 12.96/13.18      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['90'])).
% 12.96/13.18  thf('95', plain,
% 12.96/13.18      ((((k1_xboole_0) = (sk_C)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 12.96/13.18  thf('96', plain,
% 12.96/13.18      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['82', '95'])).
% 12.96/13.18  thf('97', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('98', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('99', plain,
% 12.96/13.18      ((((k1_xboole_0) = (sk_C)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 12.96/13.18  thf('100', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 12.96/13.18  thf('101', plain,
% 12.96/13.18      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['99', '100'])).
% 12.96/13.18  thf('102', plain,
% 12.96/13.18      ((((sk_B) = (k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['79', '80'])).
% 12.96/13.18  thf('103', plain,
% 12.96/13.18      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['101', '102'])).
% 12.96/13.18  thf('104', plain,
% 12.96/13.18      (![X43 : $i]:
% 12.96/13.18         ((m1_subset_1 @ X43 @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 12.96/13.18          | ~ (v1_funct_1 @ X43)
% 12.96/13.18          | ~ (v1_relat_1 @ X43))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 12.96/13.18  thf('105', plain,
% 12.96/13.18      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 12.96/13.18          (k1_zfmisc_1 @ 
% 12.96/13.18           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 12.96/13.18            (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 12.96/13.18         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 12.96/13.18         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['103', '104'])).
% 12.96/13.18  thf('106', plain,
% 12.96/13.18      (![X5 : $i, X6 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 12.96/13.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 12.96/13.18  thf('107', plain,
% 12.96/13.18      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['106'])).
% 12.96/13.18  thf('108', plain,
% 12.96/13.18      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 12.96/13.18          (k1_zfmisc_1 @ k1_xboole_0))
% 12.96/13.18         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 12.96/13.18         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['105', '107'])).
% 12.96/13.18  thf('109', plain,
% 12.96/13.18      (((~ (v1_relat_1 @ k1_xboole_0)
% 12.96/13.18         | ~ (v1_funct_1 @ k1_xboole_0)
% 12.96/13.18         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 12.96/13.18         | (m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 12.96/13.18            (k1_zfmisc_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['98', '108'])).
% 12.96/13.18  thf(t4_subset_1, axiom,
% 12.96/13.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.96/13.18  thf('110', plain,
% 12.96/13.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 12.96/13.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.96/13.18  thf('111', plain,
% 12.96/13.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 12.96/13.18         ((v1_relat_1 @ X20)
% 12.96/13.18          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 12.96/13.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.96/13.18  thf('112', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.96/13.18      inference('sup-', [status(thm)], ['110', '111'])).
% 12.96/13.18  thf('113', plain,
% 12.96/13.18      ((((k1_xboole_0) = (sk_C)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['89', '91', '92', '93', '94'])).
% 12.96/13.18  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('115', plain,
% 12.96/13.18      (((v1_funct_1 @ k1_xboole_0))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['113', '114'])).
% 12.96/13.18  thf('116', plain,
% 12.96/13.18      (((~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 12.96/13.18         | (m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 12.96/13.18            (k1_zfmisc_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['109', '112', '115'])).
% 12.96/13.18  thf('117', plain,
% 12.96/13.18      (((~ (v1_relat_1 @ k1_xboole_0)
% 12.96/13.18         | ~ (v1_funct_1 @ k1_xboole_0)
% 12.96/13.18         | (m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 12.96/13.18            (k1_zfmisc_1 @ k1_xboole_0))))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['97', '116'])).
% 12.96/13.18  thf('118', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.96/13.18      inference('sup-', [status(thm)], ['110', '111'])).
% 12.96/13.18  thf('119', plain,
% 12.96/13.18      (((v1_funct_1 @ k1_xboole_0))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['113', '114'])).
% 12.96/13.18  thf('120', plain,
% 12.96/13.18      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['117', '118', '119'])).
% 12.96/13.18  thf('121', plain,
% 12.96/13.18      (![X8 : $i, X9 : $i]:
% 12.96/13.18         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_subset])).
% 12.96/13.18  thf('122', plain,
% 12.96/13.18      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['120', '121'])).
% 12.96/13.18  thf('123', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.96/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.96/13.18  thf('124', plain,
% 12.96/13.18      (![X0 : $i, X2 : $i]:
% 12.96/13.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.96/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.96/13.18  thf('125', plain,
% 12.96/13.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['123', '124'])).
% 12.96/13.18  thf('126', plain,
% 12.96/13.18      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 12.96/13.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['122', '125'])).
% 12.96/13.18  thf('127', plain,
% 12.96/13.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 12.96/13.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.96/13.18  thf('128', plain,
% 12.96/13.18      (![X26 : $i, X27 : $i, X28 : $i]:
% 12.96/13.18         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 12.96/13.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 12.96/13.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.96/13.18  thf('129', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]:
% 12.96/13.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 12.96/13.18      inference('sup-', [status(thm)], ['127', '128'])).
% 12.96/13.18  thf('130', plain,
% 12.96/13.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 12.96/13.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.96/13.18  thf(cc2_relset_1, axiom,
% 12.96/13.18    (![A:$i,B:$i,C:$i]:
% 12.96/13.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.96/13.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 12.96/13.18  thf('131', plain,
% 12.96/13.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.96/13.18         ((v4_relat_1 @ X23 @ X24)
% 12.96/13.18          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 12.96/13.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.96/13.18  thf('132', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 12.96/13.18      inference('sup-', [status(thm)], ['130', '131'])).
% 12.96/13.18  thf('133', plain,
% 12.96/13.18      (![X14 : $i, X15 : $i]:
% 12.96/13.18         (~ (v4_relat_1 @ X14 @ X15)
% 12.96/13.18          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 12.96/13.18          | ~ (v1_relat_1 @ X14))),
% 12.96/13.18      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.96/13.18  thf('134', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_relat_1 @ k1_xboole_0)
% 12.96/13.18          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 12.96/13.18      inference('sup-', [status(thm)], ['132', '133'])).
% 12.96/13.18  thf('135', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.96/13.18      inference('sup-', [status(thm)], ['110', '111'])).
% 12.96/13.18  thf('136', plain,
% 12.96/13.18      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 12.96/13.18      inference('demod', [status(thm)], ['134', '135'])).
% 12.96/13.18  thf('137', plain,
% 12.96/13.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['123', '124'])).
% 12.96/13.18  thf('138', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.96/13.18      inference('sup-', [status(thm)], ['136', '137'])).
% 12.96/13.18  thf('139', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]:
% 12.96/13.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.96/13.18      inference('demod', [status(thm)], ['129', '138'])).
% 12.96/13.18  thf('140', plain,
% 12.96/13.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.96/13.18         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 12.96/13.18          | (v1_funct_2 @ X36 @ X34 @ X35)
% 12.96/13.18          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.96/13.18  thf('141', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]:
% 12.96/13.18         (((X1) != (k1_xboole_0))
% 12.96/13.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 12.96/13.18          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 12.96/13.18      inference('sup-', [status(thm)], ['139', '140'])).
% 12.96/13.18  thf('142', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 12.96/13.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['141'])).
% 12.96/13.18  thf('143', plain,
% 12.96/13.18      (![X32 : $i, X33 : $i]:
% 12.96/13.18         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.96/13.18  thf('144', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 12.96/13.18      inference('simplify', [status(thm)], ['143'])).
% 12.96/13.18  thf('145', plain,
% 12.96/13.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 12.96/13.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.96/13.18  thf('146', plain,
% 12.96/13.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 12.96/13.18         (~ (zip_tseitin_0 @ X37 @ X38)
% 12.96/13.18          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 12.96/13.18          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.96/13.18  thf('147', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]:
% 12.96/13.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 12.96/13.18      inference('sup-', [status(thm)], ['145', '146'])).
% 12.96/13.18  thf('148', plain,
% 12.96/13.18      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 12.96/13.18      inference('sup-', [status(thm)], ['144', '147'])).
% 12.96/13.18  thf('149', plain,
% 12.96/13.18      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 12.96/13.18      inference('demod', [status(thm)], ['142', '148'])).
% 12.96/13.18  thf('150', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 12.96/13.18      inference('demod', [status(thm)], ['96', '126', '149'])).
% 12.96/13.18  thf('151', plain,
% 12.96/13.18      (~
% 12.96/13.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 12.96/13.18       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 12.96/13.18       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('split', [status(esa)], ['0'])).
% 12.96/13.18  thf('152', plain,
% 12.96/13.18      (~
% 12.96/13.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.96/13.18      inference('sat_resolution*', [status(thm)], ['10', '150', '151'])).
% 12.96/13.18  thf('153', plain,
% 12.96/13.18      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.96/13.18      inference('simpl_trail', [status(thm)], ['1', '152'])).
% 12.96/13.18  thf('154', plain,
% 12.96/13.18      (![X19 : $i]:
% 12.96/13.18         (~ (v2_funct_1 @ X19)
% 12.96/13.18          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 12.96/13.18          | ~ (v1_funct_1 @ X19)
% 12.96/13.18          | ~ (v1_relat_1 @ X19))),
% 12.96/13.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.96/13.18  thf('155', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('156', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('157', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 12.96/13.18  thf('158', plain,
% 12.96/13.18      (![X43 : $i]:
% 12.96/13.18         ((m1_subset_1 @ X43 @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 12.96/13.18          | ~ (v1_funct_1 @ X43)
% 12.96/13.18          | ~ (v1_relat_1 @ X43))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 12.96/13.18  thf('159', plain,
% 12.96/13.18      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18         (k1_zfmisc_1 @ 
% 12.96/13.18          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 12.96/13.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('sup+', [status(thm)], ['157', '158'])).
% 12.96/13.18  thf('160', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['156', '159'])).
% 12.96/13.18  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('163', plain,
% 12.96/13.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 12.96/13.18      inference('demod', [status(thm)], ['160', '161', '162'])).
% 12.96/13.18  thf('164', plain,
% 12.96/13.18      ((~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 12.96/13.18      inference('sup-', [status(thm)], ['155', '163'])).
% 12.96/13.18  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('167', plain,
% 12.96/13.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18        (k1_zfmisc_1 @ 
% 12.96/13.18         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 12.96/13.18      inference('demod', [status(thm)], ['164', '165', '166'])).
% 12.96/13.18  thf('168', plain,
% 12.96/13.18      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 12.96/13.18        | ~ (v1_relat_1 @ sk_C)
% 12.96/13.18        | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18        | ~ (v2_funct_1 @ sk_C))),
% 12.96/13.18      inference('sup+', [status(thm)], ['154', '167'])).
% 12.96/13.18  thf('169', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('170', plain,
% 12.96/13.18      (![X18 : $i]:
% 12.96/13.18         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 12.96/13.18          | ~ (v1_funct_1 @ X18)
% 12.96/13.18          | ~ (v1_relat_1 @ X18))),
% 12.96/13.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.96/13.18  thf('171', plain,
% 12.96/13.18      (![X32 : $i, X33 : $i]:
% 12.96/13.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.96/13.18  thf('172', plain,
% 12.96/13.18      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 12.96/13.18      inference('simplify', [status(thm)], ['106'])).
% 12.96/13.18  thf('173', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 12.96/13.18      inference('sup+', [status(thm)], ['171', '172'])).
% 12.96/13.18  thf('174', plain,
% 12.96/13.18      (![X43 : $i]:
% 12.96/13.18         ((m1_subset_1 @ X43 @ 
% 12.96/13.18           (k1_zfmisc_1 @ 
% 12.96/13.18            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 12.96/13.18          | ~ (v1_funct_1 @ X43)
% 12.96/13.18          | ~ (v1_relat_1 @ X43))),
% 12.96/13.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 12.96/13.18  thf('175', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i]:
% 12.96/13.18         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 12.96/13.18          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 12.96/13.18          | ~ (v1_relat_1 @ X0)
% 12.96/13.18          | ~ (v1_funct_1 @ X0))),
% 12.96/13.18      inference('sup+', [status(thm)], ['173', '174'])).
% 12.96/13.18  thf('176', plain,
% 12.96/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 12.96/13.18      inference('sup+', [status(thm)], ['171', '172'])).
% 12.96/13.18  thf('177', plain,
% 12.96/13.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['13', '14'])).
% 12.96/13.18  thf('178', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 12.96/13.18          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['176', '177'])).
% 12.96/13.18  thf('179', plain,
% 12.96/13.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['19', '22'])).
% 12.96/13.18  thf('180', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 12.96/13.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['178', '179'])).
% 12.96/13.18  thf('181', plain,
% 12.96/13.18      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.96/13.18      inference('simpl_trail', [status(thm)], ['1', '152'])).
% 12.96/13.18  thf('182', plain,
% 12.96/13.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 12.96/13.18        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['180', '181'])).
% 12.96/13.18  thf('183', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18          | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 12.96/13.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['175', '182'])).
% 12.96/13.18  thf('184', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 12.96/13.18  thf('185', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.96/13.18          | (zip_tseitin_0 @ sk_B @ X0)
% 12.96/13.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['183', '184'])).
% 12.96/13.18  thf('186', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_relat_1 @ sk_C)
% 12.96/13.18          | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18          | ((sk_A) = (k1_relat_1 @ sk_C))
% 12.96/13.18          | (zip_tseitin_0 @ sk_B @ X0)
% 12.96/13.18          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['170', '185'])).
% 12.96/13.18  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('189', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (((sk_A) = (k1_relat_1 @ sk_C))
% 12.96/13.18          | (zip_tseitin_0 @ sk_B @ X0)
% 12.96/13.18          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['186', '187', '188'])).
% 12.96/13.18  thf('190', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         (~ (v1_relat_1 @ sk_C)
% 12.96/13.18          | ~ (v1_funct_1 @ sk_C)
% 12.96/13.18          | (zip_tseitin_0 @ sk_B @ X0)
% 12.96/13.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('sup-', [status(thm)], ['169', '189'])).
% 12.96/13.18  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('193', plain,
% 12.96/13.18      (![X0 : $i]:
% 12.96/13.18         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['190', '191', '192'])).
% 12.96/13.18  thf('194', plain,
% 12.96/13.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['13', '14'])).
% 12.96/13.18  thf('195', plain,
% 12.96/13.18      ((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.96/13.18      inference('sup-', [status(thm)], ['193', '194'])).
% 12.96/13.18  thf('196', plain,
% 12.96/13.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.96/13.18      inference('demod', [status(thm)], ['19', '22'])).
% 12.96/13.18  thf('197', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 12.96/13.18      inference('clc', [status(thm)], ['195', '196'])).
% 12.96/13.18  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 12.96/13.18      inference('sup-', [status(thm)], ['2', '3'])).
% 12.96/13.18  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 12.96/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.96/13.18  thf('201', plain,
% 12.96/13.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.96/13.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.96/13.18      inference('demod', [status(thm)], ['168', '197', '198', '199', '200'])).
% 12.96/13.18  thf('202', plain, ($false), inference('demod', [status(thm)], ['153', '201'])).
% 12.96/13.18  
% 12.96/13.18  % SZS output end Refutation
% 12.96/13.18  
% 12.96/13.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
