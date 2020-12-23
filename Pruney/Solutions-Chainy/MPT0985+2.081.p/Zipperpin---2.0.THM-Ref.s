%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ls5zuyaH9V

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:37 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  256 (9804 expanded)
%              Number of leaves         :   41 (2959 expanded)
%              Depth                    :   36
%              Number of atoms          : 1894 (148357 expanded)
%              Number of equality atoms :  103 (5761 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_B @ sk_C )
      | ( sk_B = sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( sk_B = sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('46',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('47',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('54',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X38: $i] :
      ( ( v1_funct_2 @ X38 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('83',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['42','96'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','99'])).

thf('101',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('102',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('110',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','99'])).

thf('111',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('113',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','111','112'])).

thf('114',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('115',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('116',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('117',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('119',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('120',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('121',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('122',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('126',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('128',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('131',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('132',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['124','126','129','130','131'])).

thf('133',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','132'])).

thf('134',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('135',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('136',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('141',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['133','136','141'])).

thf('143',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('144',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('147',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('148',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('152',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('154',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','156'])).

thf('158',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('162',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('164',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['160','166'])).

thf('168',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['113','142','167'])).

thf('169',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','168','169'])).

thf('171',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','170'])).

thf('172',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('173',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('174',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('175',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('176',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_funct_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    r1_tarski @ ( k2_funct_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','180'])).

thf('182',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('183',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('184',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('187',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('191',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('195',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['195'])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['182','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('202',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('204',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','168','169'])).

thf('206',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['204','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    r1_tarski @ ( k2_funct_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['181','206','207','208','209'])).

thf('211',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('212',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    $false ),
    inference(demod,[status(thm)],['171','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ls5zuyaH9V
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:13:15 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.17/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.32  % Number of cores: 8
% 0.17/0.33  % Python version: Python 3.6.8
% 0.17/0.33  % Running in FO mode
% 1.51/1.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.76  % Solved by: fo/fo7.sh
% 1.51/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.76  % done 2366 iterations in 1.325s
% 1.51/1.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.76  % SZS output start Refutation
% 1.51/1.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.51/1.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.51/1.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.51/1.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.51/1.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.51/1.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.51/1.76  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.76  thf(t31_funct_2, conjecture,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.76       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.51/1.76         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.51/1.76           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.51/1.76           ( m1_subset_1 @
% 1.51/1.76             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.51/1.76  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.76    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.76          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.51/1.76            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.51/1.76              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.51/1.76              ( m1_subset_1 @
% 1.51/1.76                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.51/1.76    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.51/1.76  thf('0', plain,
% 1.51/1.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.51/1.76        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('1', plain,
% 1.51/1.76      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf('2', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(cc1_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( v1_relat_1 @ C ) ))).
% 1.51/1.76  thf('3', plain,
% 1.51/1.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.76         ((v1_relat_1 @ X18)
% 1.51/1.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.51/1.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.76  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf(dt_k2_funct_1, axiom,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.51/1.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.51/1.76  thf('5', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('6', plain,
% 1.51/1.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf('7', plain,
% 1.51/1.76      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.76  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('9', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('demod', [status(thm)], ['7', '8'])).
% 1.51/1.76  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['4', '9'])).
% 1.51/1.76  thf('11', plain,
% 1.51/1.76      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf(d1_funct_2, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.51/1.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.51/1.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.51/1.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.51/1.76  thf(zf_stmt_1, axiom,
% 1.51/1.76    (![B:$i,A:$i]:
% 1.51/1.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.76       ( zip_tseitin_0 @ B @ A ) ))).
% 1.51/1.76  thf('12', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf('13', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf(t113_zfmisc_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.51/1.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.51/1.76  thf('14', plain,
% 1.51/1.76      (![X4 : $i, X5 : $i]:
% 1.51/1.76         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.51/1.76  thf('15', plain,
% 1.51/1.76      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['14'])).
% 1.51/1.76  thf('16', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.76      inference('sup+', [status(thm)], ['13', '15'])).
% 1.51/1.76  thf('17', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('18', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.51/1.76          | (zip_tseitin_0 @ sk_B @ X0))),
% 1.51/1.76      inference('sup+', [status(thm)], ['16', '17'])).
% 1.51/1.76  thf('19', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.51/1.76          | (zip_tseitin_0 @ X0 @ X2)
% 1.51/1.76          | (zip_tseitin_0 @ sk_B @ X1))),
% 1.51/1.76      inference('sup+', [status(thm)], ['12', '18'])).
% 1.51/1.76  thf('20', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ sk_B @ X0)
% 1.51/1.76          | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))),
% 1.51/1.76      inference('eq_fact', [status(thm)], ['19'])).
% 1.51/1.76  thf(t3_subset, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.76  thf('21', plain,
% 1.51/1.76      (![X7 : $i, X8 : $i]:
% 1.51/1.76         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('22', plain,
% 1.51/1.76      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 1.51/1.76      inference('sup-', [status(thm)], ['20', '21'])).
% 1.51/1.76  thf(d10_xboole_0, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.76  thf('23', plain,
% 1.51/1.76      (![X0 : $i, X2 : $i]:
% 1.51/1.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('24', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ sk_B @ X0)
% 1.51/1.76          | ~ (r1_tarski @ sk_B @ sk_C)
% 1.51/1.76          | ((sk_B) = (sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['22', '23'])).
% 1.51/1.76  thf('25', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf(t4_subset_1, axiom,
% 1.51/1.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.51/1.76  thf('26', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf('27', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.76      inference('sup+', [status(thm)], ['25', '26'])).
% 1.51/1.76  thf('28', plain,
% 1.51/1.76      (![X7 : $i, X8 : $i]:
% 1.51/1.76         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('29', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.76  thf('30', plain,
% 1.51/1.76      (![X0 : $i]: (((sk_B) = (sk_C)) | (zip_tseitin_0 @ sk_B @ X0))),
% 1.51/1.76      inference('clc', [status(thm)], ['24', '29'])).
% 1.51/1.76  thf('31', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.51/1.76  thf(zf_stmt_3, axiom,
% 1.51/1.76    (![C:$i,B:$i,A:$i]:
% 1.51/1.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.51/1.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.51/1.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.51/1.76  thf(zf_stmt_5, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.51/1.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.51/1.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.51/1.76  thf('32', plain,
% 1.51/1.76      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.76         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.51/1.76          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.51/1.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.76  thf('33', plain,
% 1.51/1.76      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['31', '32'])).
% 1.51/1.76  thf('34', plain,
% 1.51/1.76      ((((sk_B) = (sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['30', '33'])).
% 1.51/1.76  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('36', plain,
% 1.51/1.76      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.51/1.76         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.51/1.76          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 1.51/1.76          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.76  thf('37', plain,
% 1.51/1.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.51/1.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['35', '36'])).
% 1.51/1.76  thf('38', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.76  thf('39', plain,
% 1.51/1.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.51/1.76         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 1.51/1.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.76  thf('40', plain,
% 1.51/1.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.76  thf('41', plain,
% 1.51/1.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['37', '40'])).
% 1.51/1.76  thf('42', plain, ((((sk_B) = (sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['34', '41'])).
% 1.51/1.76  thf(t55_funct_1, axiom,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.76       ( ( v2_funct_1 @ A ) =>
% 1.51/1.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.51/1.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.51/1.76  thf('43', plain,
% 1.51/1.76      (![X17 : $i]:
% 1.51/1.76         (~ (v2_funct_1 @ X17)
% 1.51/1.76          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.51/1.76          | ~ (v1_funct_1 @ X17)
% 1.51/1.76          | ~ (v1_relat_1 @ X17))),
% 1.51/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.76  thf('44', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('45', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('46', plain,
% 1.51/1.76      (![X17 : $i]:
% 1.51/1.76         (~ (v2_funct_1 @ X17)
% 1.51/1.76          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.51/1.76          | ~ (v1_funct_1 @ X17)
% 1.51/1.76          | ~ (v1_relat_1 @ X17))),
% 1.51/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.76  thf('47', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('48', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(redefinition_k2_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.51/1.76  thf('49', plain,
% 1.51/1.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.51/1.76         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 1.51/1.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.76  thf('50', plain,
% 1.51/1.76      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.51/1.76      inference('sup-', [status(thm)], ['48', '49'])).
% 1.51/1.76  thf('51', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.51/1.76      inference('sup+', [status(thm)], ['50', '51'])).
% 1.51/1.76  thf('53', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('54', plain,
% 1.51/1.76      (![X17 : $i]:
% 1.51/1.76         (~ (v2_funct_1 @ X17)
% 1.51/1.76          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.51/1.76          | ~ (v1_funct_1 @ X17)
% 1.51/1.76          | ~ (v1_relat_1 @ X17))),
% 1.51/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.76  thf('55', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.51/1.76      inference('simplify', [status(thm)], ['55'])).
% 1.51/1.76  thf(d18_relat_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( v1_relat_1 @ B ) =>
% 1.51/1.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.51/1.76  thf('57', plain,
% 1.51/1.76      (![X13 : $i, X14 : $i]:
% 1.51/1.76         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.51/1.76          | (v4_relat_1 @ X13 @ X14)
% 1.51/1.76          | ~ (v1_relat_1 @ X13))),
% 1.51/1.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.51/1.76  thf('58', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['56', '57'])).
% 1.51/1.76  thf('59', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.51/1.76          | ~ (v1_relat_1 @ X0)
% 1.51/1.76          | ~ (v1_funct_1 @ X0)
% 1.51/1.76          | ~ (v2_funct_1 @ X0)
% 1.51/1.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['54', '58'])).
% 1.51/1.76  thf('60', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ X0)
% 1.51/1.76          | ~ (v1_funct_1 @ X0)
% 1.51/1.76          | ~ (v2_funct_1 @ X0)
% 1.51/1.76          | ~ (v1_funct_1 @ X0)
% 1.51/1.76          | ~ (v1_relat_1 @ X0)
% 1.51/1.76          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['53', '59'])).
% 1.51/1.76  thf('61', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.51/1.76          | ~ (v2_funct_1 @ X0)
% 1.51/1.76          | ~ (v1_funct_1 @ X0)
% 1.51/1.76          | ~ (v1_relat_1 @ X0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['60'])).
% 1.51/1.76  thf('62', plain,
% 1.51/1.76      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.51/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.76      inference('sup+', [status(thm)], ['52', '61'])).
% 1.51/1.76  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('66', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.51/1.76      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 1.51/1.76  thf('67', plain,
% 1.51/1.76      (![X13 : $i, X14 : $i]:
% 1.51/1.76         (~ (v4_relat_1 @ X13 @ X14)
% 1.51/1.76          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.51/1.76          | ~ (v1_relat_1 @ X13))),
% 1.51/1.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.51/1.76  thf('68', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.51/1.76      inference('sup-', [status(thm)], ['66', '67'])).
% 1.51/1.76  thf('69', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.51/1.76      inference('sup-', [status(thm)], ['47', '68'])).
% 1.51/1.76  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('72', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.51/1.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.51/1.76  thf('73', plain,
% 1.51/1.76      (![X0 : $i, X2 : $i]:
% 1.51/1.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('74', plain,
% 1.51/1.76      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.51/1.76        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.76  thf('75', plain,
% 1.51/1.76      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.51/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.51/1.76        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['46', '74'])).
% 1.51/1.76  thf('76', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.51/1.76      inference('sup+', [status(thm)], ['50', '51'])).
% 1.51/1.76  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.51/1.76      inference('simplify', [status(thm)], ['55'])).
% 1.51/1.76  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('81', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 1.51/1.76  thf(t3_funct_2, axiom,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.76       ( ( v1_funct_1 @ A ) & 
% 1.51/1.76         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.51/1.76         ( m1_subset_1 @
% 1.51/1.76           A @ 
% 1.51/1.76           ( k1_zfmisc_1 @
% 1.51/1.76             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.76  thf('82', plain,
% 1.51/1.76      (![X38 : $i]:
% 1.51/1.76         ((v1_funct_2 @ X38 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))
% 1.51/1.76          | ~ (v1_funct_1 @ X38)
% 1.51/1.76          | ~ (v1_relat_1 @ X38))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.51/1.76  thf('83', plain,
% 1.51/1.76      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.51/1.76         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.51/1.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['81', '82'])).
% 1.51/1.76  thf('84', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.51/1.76           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['45', '83'])).
% 1.51/1.76  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('87', plain,
% 1.51/1.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.51/1.76           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.51/1.76  thf('88', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.51/1.76           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['44', '87'])).
% 1.51/1.76  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('91', plain,
% 1.51/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.51/1.76        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.51/1.76  thf('92', plain,
% 1.51/1.76      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 1.51/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.76      inference('sup+', [status(thm)], ['43', '91'])).
% 1.51/1.76  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('96', plain,
% 1.51/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 1.51/1.76  thf('97', plain,
% 1.51/1.76      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['42', '96'])).
% 1.51/1.76  thf('98', plain,
% 1.51/1.76      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf('99', plain,
% 1.51/1.76      ((((sk_B) = (sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['97', '98'])).
% 1.51/1.76  thf('100', plain,
% 1.51/1.76      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['11', '99'])).
% 1.51/1.76  thf('101', plain,
% 1.51/1.76      ((((sk_B) = (sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['97', '98'])).
% 1.51/1.76  thf('102', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf('103', plain,
% 1.51/1.76      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['31', '32'])).
% 1.51/1.76  thf('104', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['102', '103'])).
% 1.51/1.76  thf('105', plain,
% 1.51/1.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['37', '40'])).
% 1.51/1.76  thf('106', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['104', '105'])).
% 1.51/1.76  thf('107', plain,
% 1.51/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 1.51/1.76  thf('108', plain,
% 1.51/1.76      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.51/1.76        | ((sk_B) = (k1_xboole_0)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['106', '107'])).
% 1.51/1.76  thf('109', plain,
% 1.51/1.76      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 1.51/1.76         | ((sk_B) = (k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['101', '108'])).
% 1.51/1.76  thf('110', plain,
% 1.51/1.76      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['11', '99'])).
% 1.51/1.76  thf('111', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('clc', [status(thm)], ['109', '110'])).
% 1.51/1.76  thf('112', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('clc', [status(thm)], ['109', '110'])).
% 1.51/1.76  thf('113', plain,
% 1.51/1.76      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['100', '111', '112'])).
% 1.51/1.76  thf('114', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('115', plain,
% 1.51/1.76      ((((sk_B) = (sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['97', '98'])).
% 1.51/1.76  thf('116', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 1.51/1.76  thf('117', plain,
% 1.51/1.76      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_B))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['115', '116'])).
% 1.51/1.76  thf('118', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('clc', [status(thm)], ['109', '110'])).
% 1.51/1.76  thf('119', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('clc', [status(thm)], ['109', '110'])).
% 1.51/1.76  thf('120', plain,
% 1.51/1.76      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.51/1.76  thf(t21_relat_1, axiom,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( v1_relat_1 @ A ) =>
% 1.51/1.76       ( r1_tarski @
% 1.51/1.76         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.51/1.76  thf('121', plain,
% 1.51/1.76      (![X15 : $i]:
% 1.51/1.76         ((r1_tarski @ X15 @ 
% 1.51/1.76           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 1.51/1.76          | ~ (v1_relat_1 @ X15))),
% 1.51/1.76      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.51/1.76  thf('122', plain,
% 1.51/1.76      (![X0 : $i, X2 : $i]:
% 1.51/1.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('123', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ X0)
% 1.51/1.76          | ~ (r1_tarski @ 
% 1.51/1.76               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 1.51/1.76          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['121', '122'])).
% 1.51/1.76  thf('124', plain,
% 1.51/1.76      (((~ (r1_tarski @ 
% 1.51/1.76            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 1.51/1.76             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))) @ 
% 1.51/1.76            (k2_funct_1 @ k1_xboole_0))
% 1.51/1.76         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 1.51/1.76             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 1.51/1.76             = (k2_funct_1 @ k1_xboole_0))
% 1.51/1.76         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['120', '123'])).
% 1.51/1.76  thf('125', plain,
% 1.51/1.76      (![X4 : $i, X5 : $i]:
% 1.51/1.76         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.51/1.76  thf('126', plain,
% 1.51/1.76      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['125'])).
% 1.51/1.76  thf('127', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf('128', plain,
% 1.51/1.76      (![X7 : $i, X8 : $i]:
% 1.51/1.76         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('129', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.51/1.76      inference('sup-', [status(thm)], ['127', '128'])).
% 1.51/1.76  thf('130', plain,
% 1.51/1.76      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.51/1.76  thf('131', plain,
% 1.51/1.76      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['125'])).
% 1.51/1.76  thf('132', plain,
% 1.51/1.76      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 1.51/1.76         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['124', '126', '129', '130', '131'])).
% 1.51/1.76  thf('133', plain,
% 1.51/1.76      (((~ (v1_relat_1 @ k1_xboole_0)
% 1.51/1.76         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.51/1.76         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['114', '132'])).
% 1.51/1.76  thf('134', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf('135', plain,
% 1.51/1.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.76         ((v1_relat_1 @ X18)
% 1.51/1.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.51/1.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.76  thf('136', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.51/1.76      inference('sup-', [status(thm)], ['134', '135'])).
% 1.51/1.76  thf('137', plain,
% 1.51/1.76      ((((sk_B) = (sk_C)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['97', '98'])).
% 1.51/1.76  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('139', plain,
% 1.51/1.76      (((v1_funct_1 @ sk_B))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['137', '138'])).
% 1.51/1.76  thf('140', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('clc', [status(thm)], ['109', '110'])).
% 1.51/1.76  thf('141', plain,
% 1.51/1.76      (((v1_funct_1 @ k1_xboole_0))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['139', '140'])).
% 1.51/1.76  thf('142', plain,
% 1.51/1.76      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 1.51/1.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.76      inference('demod', [status(thm)], ['133', '136', '141'])).
% 1.51/1.76  thf('143', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf('144', plain,
% 1.51/1.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.51/1.76         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 1.51/1.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.76  thf('145', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['143', '144'])).
% 1.51/1.76  thf('146', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf(cc2_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.51/1.76  thf('147', plain,
% 1.51/1.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.51/1.76         ((v4_relat_1 @ X21 @ X22)
% 1.51/1.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.51/1.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.51/1.76  thf('148', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.51/1.76      inference('sup-', [status(thm)], ['146', '147'])).
% 1.51/1.76  thf('149', plain,
% 1.51/1.76      (![X13 : $i, X14 : $i]:
% 1.51/1.76         (~ (v4_relat_1 @ X13 @ X14)
% 1.51/1.76          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.51/1.76          | ~ (v1_relat_1 @ X13))),
% 1.51/1.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.51/1.76  thf('150', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ k1_xboole_0)
% 1.51/1.76          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['148', '149'])).
% 1.51/1.76  thf('151', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.51/1.76      inference('sup-', [status(thm)], ['134', '135'])).
% 1.51/1.76  thf('152', plain,
% 1.51/1.76      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.51/1.76      inference('demod', [status(thm)], ['150', '151'])).
% 1.51/1.76  thf('153', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.51/1.76      inference('sup-', [status(thm)], ['127', '128'])).
% 1.51/1.76  thf('154', plain,
% 1.51/1.76      (![X0 : $i, X2 : $i]:
% 1.51/1.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('155', plain,
% 1.51/1.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['153', '154'])).
% 1.51/1.76  thf('156', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['152', '155'])).
% 1.51/1.76  thf('157', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.76      inference('demod', [status(thm)], ['145', '156'])).
% 1.51/1.76  thf('158', plain,
% 1.51/1.76      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.51/1.76         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 1.51/1.76          | (v1_funct_2 @ X34 @ X32 @ X33)
% 1.51/1.76          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.76  thf('159', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         (((X1) != (k1_xboole_0))
% 1.51/1.76          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.51/1.76          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['157', '158'])).
% 1.51/1.76  thf('160', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.51/1.76          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['159'])).
% 1.51/1.76  thf('161', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf('162', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 1.51/1.76      inference('simplify', [status(thm)], ['161'])).
% 1.51/1.76  thf('163', plain,
% 1.51/1.76      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.76  thf('164', plain,
% 1.51/1.76      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.76         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.51/1.76          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.51/1.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.76  thf('165', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.51/1.76      inference('sup-', [status(thm)], ['163', '164'])).
% 1.51/1.76  thf('166', plain,
% 1.51/1.76      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.51/1.76      inference('sup-', [status(thm)], ['162', '165'])).
% 1.51/1.76  thf('167', plain,
% 1.51/1.76      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.51/1.76      inference('demod', [status(thm)], ['160', '166'])).
% 1.51/1.76  thf('168', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.51/1.76      inference('demod', [status(thm)], ['113', '142', '167'])).
% 1.51/1.76  thf('169', plain,
% 1.51/1.76      (~
% 1.51/1.76       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.51/1.76       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.51/1.76       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf('170', plain,
% 1.51/1.76      (~
% 1.51/1.76       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.76      inference('sat_resolution*', [status(thm)], ['10', '168', '169'])).
% 1.51/1.76  thf('171', plain,
% 1.51/1.76      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.76      inference('simpl_trail', [status(thm)], ['1', '170'])).
% 1.51/1.76  thf('172', plain,
% 1.51/1.76      (![X17 : $i]:
% 1.51/1.76         (~ (v2_funct_1 @ X17)
% 1.51/1.76          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.51/1.76          | ~ (v1_funct_1 @ X17)
% 1.51/1.76          | ~ (v1_relat_1 @ X17))),
% 1.51/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.76  thf('173', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('174', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 1.51/1.76  thf('175', plain,
% 1.51/1.76      (![X15 : $i]:
% 1.51/1.76         ((r1_tarski @ X15 @ 
% 1.51/1.76           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 1.51/1.76          | ~ (v1_relat_1 @ X15))),
% 1.51/1.76      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.51/1.76  thf('176', plain,
% 1.51/1.76      (((r1_tarski @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.51/1.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['174', '175'])).
% 1.51/1.76  thf('177', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | (r1_tarski @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['173', '176'])).
% 1.51/1.76  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('180', plain,
% 1.51/1.76      ((r1_tarski @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76        (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.76      inference('demod', [status(thm)], ['177', '178', '179'])).
% 1.51/1.76  thf('181', plain,
% 1.51/1.76      (((r1_tarski @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76         (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))
% 1.51/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.76      inference('sup+', [status(thm)], ['172', '180'])).
% 1.51/1.76  thf('182', plain,
% 1.51/1.76      (![X16 : $i]:
% 1.51/1.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.51/1.76          | ~ (v1_funct_1 @ X16)
% 1.51/1.76          | ~ (v1_relat_1 @ X16))),
% 1.51/1.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.76  thf('183', plain,
% 1.51/1.76      (![X30 : $i, X31 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf('184', plain,
% 1.51/1.76      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.51/1.76      inference('simplify', [status(thm)], ['125'])).
% 1.51/1.76  thf('185', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.76      inference('sup+', [status(thm)], ['183', '184'])).
% 1.51/1.76  thf('186', plain,
% 1.51/1.76      (![X15 : $i]:
% 1.51/1.76         ((r1_tarski @ X15 @ 
% 1.51/1.76           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 1.51/1.76          | ~ (v1_relat_1 @ X15))),
% 1.51/1.76      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.51/1.76  thf('187', plain,
% 1.51/1.76      (![X7 : $i, X9 : $i]:
% 1.51/1.76         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('188', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ X0)
% 1.51/1.76          | (m1_subset_1 @ X0 @ 
% 1.51/1.76             (k1_zfmisc_1 @ 
% 1.51/1.76              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['186', '187'])).
% 1.51/1.76  thf('189', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.51/1.76          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.51/1.76          | ~ (v1_relat_1 @ X0))),
% 1.51/1.76      inference('sup+', [status(thm)], ['185', '188'])).
% 1.51/1.76  thf('190', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.76      inference('sup+', [status(thm)], ['183', '184'])).
% 1.51/1.76  thf('191', plain,
% 1.51/1.76      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('split', [status(esa)], ['0'])).
% 1.51/1.76  thf('192', plain,
% 1.51/1.76      ((![X0 : $i]:
% 1.51/1.76          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.51/1.76           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['190', '191'])).
% 1.51/1.76  thf('193', plain,
% 1.51/1.76      ((![X0 : $i, X1 : $i]:
% 1.51/1.76          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X1)
% 1.51/1.76           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['189', '192'])).
% 1.51/1.76  thf('194', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 1.51/1.76  thf('195', plain,
% 1.51/1.76      ((![X0 : $i, X1 : $i]:
% 1.51/1.76          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.76           | (zip_tseitin_0 @ sk_B @ X1)
% 1.51/1.76           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('demod', [status(thm)], ['193', '194'])).
% 1.51/1.76  thf('196', plain,
% 1.51/1.76      ((![X0 : $i]:
% 1.51/1.76          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C)) | (zip_tseitin_0 @ sk_B @ X0)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('condensation', [status(thm)], ['195'])).
% 1.51/1.76  thf('197', plain,
% 1.51/1.76      ((![X0 : $i]:
% 1.51/1.76          (~ (v1_relat_1 @ sk_C)
% 1.51/1.76           | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['182', '196'])).
% 1.51/1.76  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('200', plain,
% 1.51/1.76      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.51/1.76  thf('201', plain,
% 1.51/1.76      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['31', '32'])).
% 1.51/1.76  thf('202', plain,
% 1.51/1.76      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['200', '201'])).
% 1.51/1.76  thf('203', plain,
% 1.51/1.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['37', '40'])).
% 1.51/1.76  thf('204', plain,
% 1.51/1.76      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.51/1.76         <= (~
% 1.51/1.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['202', '203'])).
% 1.51/1.76  thf('205', plain,
% 1.51/1.76      (~
% 1.51/1.76       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.76      inference('sat_resolution*', [status(thm)], ['10', '168', '169'])).
% 1.51/1.76  thf('206', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('simpl_trail', [status(thm)], ['204', '205'])).
% 1.51/1.76  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.76  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('209', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('210', plain,
% 1.51/1.76      ((r1_tarski @ (k2_funct_1 @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 1.51/1.76      inference('demod', [status(thm)], ['181', '206', '207', '208', '209'])).
% 1.51/1.76  thf('211', plain,
% 1.51/1.76      (![X7 : $i, X9 : $i]:
% 1.51/1.76         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('212', plain,
% 1.51/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['210', '211'])).
% 1.51/1.76  thf('213', plain, ($false), inference('demod', [status(thm)], ['171', '212'])).
% 1.51/1.76  
% 1.51/1.76  % SZS output end Refutation
% 1.51/1.76  
% 1.51/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
