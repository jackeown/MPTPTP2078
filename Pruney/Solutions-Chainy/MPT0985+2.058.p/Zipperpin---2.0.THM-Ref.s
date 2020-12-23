%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RahOhpfaKP

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:35 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  256 (3187 expanded)
%              Number of leaves         :   42 ( 949 expanded)
%              Depth                    :   23
%              Number of atoms          : 2130 (49231 expanded)
%              Number of equality atoms :  119 (2171 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X40: $i] :
      ( ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('64',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','61','62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','64'])).

thf('66',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','61','62','63'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('71',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['67','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('92',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('94',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','94'])).

thf('96',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','61','62','63'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('102',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X28 )
      | ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('111',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('113',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('114',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('118',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X38: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X38 ) @ X38 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('120',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['104','111','120'])).

thf('122',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('125',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('129',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('131',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','133'])).

thf('135',plain,
    ( ( ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','134'])).

thf('136',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','64'])).

thf('137',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['104','111','120'])).

thf('139',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('143',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['140','147'])).

thf('149',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','61','62','63'])).

thf('150',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','61','62','63'])).

thf('151',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','133'])).

thf('152',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','139','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','153','154'])).

thf('156',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','155'])).

thf('157',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('159',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('162',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['158','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','172'])).

thf('174',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('175',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('178',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('181',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('186',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['179','186'])).

thf('188',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['176','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['174','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199','200'])).

thf('202',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('203',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('205',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','153','154'])).

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
    inference(demod,[status(thm)],['173','207','208','209','210'])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['156','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RahOhpfaKP
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.60/1.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.77  % Solved by: fo/fo7.sh
% 1.60/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.77  % done 1847 iterations in 1.324s
% 1.60/1.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.77  % SZS output start Refutation
% 1.60/1.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.60/1.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.60/1.77  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.60/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.60/1.77  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.60/1.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.60/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.60/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.77  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.60/1.77  thf(t31_funct_2, conjecture,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.77       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.60/1.77         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.60/1.77           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.60/1.77           ( m1_subset_1 @
% 1.60/1.77             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.60/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.77    (~( ![A:$i,B:$i,C:$i]:
% 1.60/1.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.77          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.60/1.77            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.60/1.77              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.60/1.77              ( m1_subset_1 @
% 1.60/1.77                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.60/1.77    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.60/1.77  thf('0', plain,
% 1.60/1.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.60/1.77        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('1', plain,
% 1.60/1.77      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.60/1.77         <= (~
% 1.60/1.77             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.77      inference('split', [status(esa)], ['0'])).
% 1.60/1.77  thf('2', plain,
% 1.60/1.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(cc1_relset_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( v1_relat_1 @ C ) ))).
% 1.60/1.77  thf('3', plain,
% 1.60/1.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.60/1.77         ((v1_relat_1 @ X18)
% 1.60/1.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.60/1.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.77  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.77  thf(dt_k2_funct_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.77       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.60/1.77         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.60/1.77  thf('5', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.77  thf('6', plain,
% 1.60/1.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.77      inference('split', [status(esa)], ['0'])).
% 1.60/1.77  thf('7', plain,
% 1.60/1.77      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.77      inference('sup-', [status(thm)], ['5', '6'])).
% 1.60/1.77  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('9', plain,
% 1.60/1.77      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.77      inference('demod', [status(thm)], ['7', '8'])).
% 1.60/1.77  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['4', '9'])).
% 1.60/1.77  thf('11', plain,
% 1.60/1.77      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('split', [status(esa)], ['0'])).
% 1.60/1.77  thf(d1_funct_2, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.60/1.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.60/1.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.60/1.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.60/1.77  thf(zf_stmt_1, axiom,
% 1.60/1.77    (![B:$i,A:$i]:
% 1.60/1.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.77       ( zip_tseitin_0 @ B @ A ) ))).
% 1.60/1.77  thf('12', plain,
% 1.60/1.77      (![X30 : $i, X31 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.77  thf('13', plain,
% 1.60/1.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.60/1.77  thf(zf_stmt_3, axiom,
% 1.60/1.77    (![C:$i,B:$i,A:$i]:
% 1.60/1.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.60/1.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.60/1.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.60/1.77  thf(zf_stmt_5, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.60/1.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.60/1.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.60/1.77  thf('14', plain,
% 1.60/1.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.60/1.77         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.60/1.77          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.60/1.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.77  thf('15', plain,
% 1.60/1.77      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.77      inference('sup-', [status(thm)], ['13', '14'])).
% 1.60/1.77  thf('16', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.60/1.77      inference('sup-', [status(thm)], ['12', '15'])).
% 1.60/1.77  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('18', plain,
% 1.60/1.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.60/1.77         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.60/1.77          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 1.60/1.77          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.60/1.77  thf('19', plain,
% 1.60/1.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.60/1.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['17', '18'])).
% 1.60/1.77  thf('20', plain,
% 1.60/1.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(redefinition_k1_relset_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.60/1.77  thf('21', plain,
% 1.60/1.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.77         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.60/1.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.60/1.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.77  thf('22', plain,
% 1.60/1.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.60/1.77      inference('sup-', [status(thm)], ['20', '21'])).
% 1.60/1.77  thf('23', plain,
% 1.60/1.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.77      inference('demod', [status(thm)], ['19', '22'])).
% 1.60/1.77  thf('24', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['16', '23'])).
% 1.60/1.77  thf(t55_funct_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.77       ( ( v2_funct_1 @ A ) =>
% 1.60/1.77         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.60/1.77           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.60/1.77  thf('25', plain,
% 1.60/1.77      (![X17 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X17)
% 1.60/1.77          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.77          | ~ (v1_funct_1 @ X17)
% 1.60/1.77          | ~ (v1_relat_1 @ X17))),
% 1.60/1.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.77  thf('26', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.77  thf('27', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.77  thf('28', plain,
% 1.60/1.77      (![X17 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X17)
% 1.60/1.77          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.77          | ~ (v1_funct_1 @ X17)
% 1.60/1.77          | ~ (v1_relat_1 @ X17))),
% 1.60/1.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.77  thf(t3_funct_2, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.77       ( ( v1_funct_1 @ A ) & 
% 1.60/1.77         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.60/1.77         ( m1_subset_1 @
% 1.60/1.77           A @ 
% 1.60/1.77           ( k1_zfmisc_1 @
% 1.60/1.77             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.60/1.77  thf('29', plain,
% 1.60/1.77      (![X40 : $i]:
% 1.60/1.77         ((v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))
% 1.60/1.77          | ~ (v1_funct_1 @ X40)
% 1.60/1.77          | ~ (v1_relat_1 @ X40))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.77  thf('30', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.60/1.77      inference('sup+', [status(thm)], ['28', '29'])).
% 1.60/1.77  thf('31', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.60/1.77      inference('sup-', [status(thm)], ['27', '30'])).
% 1.60/1.77  thf('32', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['31'])).
% 1.60/1.77  thf('33', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.60/1.77      inference('sup-', [status(thm)], ['26', '32'])).
% 1.60/1.77  thf('34', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['33'])).
% 1.60/1.77  thf('35', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77           (k1_relat_1 @ X0))
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v2_funct_1 @ X0))),
% 1.60/1.77      inference('sup+', [status(thm)], ['25', '34'])).
% 1.60/1.77  thf('36', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77             (k1_relat_1 @ X0)))),
% 1.60/1.77      inference('simplify', [status(thm)], ['35'])).
% 1.60/1.77  thf('37', plain,
% 1.60/1.77      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.60/1.77        | ((sk_B) = (k1_xboole_0))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.77        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.77        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.77      inference('sup+', [status(thm)], ['24', '36'])).
% 1.60/1.77  thf('38', plain,
% 1.60/1.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(redefinition_k2_relset_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.60/1.77  thf('39', plain,
% 1.60/1.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.60/1.77         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 1.60/1.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.60/1.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.60/1.77  thf('40', plain,
% 1.60/1.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.60/1.77      inference('sup-', [status(thm)], ['38', '39'])).
% 1.60/1.77  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.77      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.77  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.77  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('46', plain,
% 1.60/1.77      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.60/1.77        | ((sk_B) = (k1_xboole_0)))),
% 1.60/1.77      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 1.60/1.77  thf('47', plain,
% 1.60/1.77      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('split', [status(esa)], ['0'])).
% 1.60/1.77  thf('48', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.77  thf('49', plain,
% 1.60/1.77      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['11', '48'])).
% 1.60/1.77  thf('50', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.77  thf('51', plain,
% 1.60/1.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(t3_subset, axiom,
% 1.60/1.77    (![A:$i,B:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.60/1.77  thf('52', plain,
% 1.60/1.77      (![X8 : $i, X9 : $i]:
% 1.60/1.77         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.77  thf('53', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.60/1.77      inference('sup-', [status(thm)], ['51', '52'])).
% 1.60/1.77  thf(d10_xboole_0, axiom,
% 1.60/1.77    (![A:$i,B:$i]:
% 1.60/1.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.60/1.77  thf('54', plain,
% 1.60/1.77      (![X0 : $i, X2 : $i]:
% 1.60/1.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.77  thf('55', plain,
% 1.60/1.77      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 1.60/1.77        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.77  thf('56', plain,
% 1.60/1.77      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 1.60/1.77         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['50', '55'])).
% 1.60/1.77  thf(t113_zfmisc_1, axiom,
% 1.60/1.77    (![A:$i,B:$i]:
% 1.60/1.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.60/1.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.60/1.77  thf('57', plain,
% 1.60/1.77      (![X5 : $i, X6 : $i]:
% 1.60/1.77         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.77  thf('58', plain,
% 1.60/1.77      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['57'])).
% 1.60/1.77  thf(t4_subset_1, axiom,
% 1.60/1.77    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.60/1.77  thf('59', plain,
% 1.60/1.77      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.77  thf('60', plain,
% 1.60/1.77      (![X8 : $i, X9 : $i]:
% 1.60/1.77         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.77  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.60/1.77      inference('sup-', [status(thm)], ['59', '60'])).
% 1.60/1.77  thf('62', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.77  thf('63', plain,
% 1.60/1.77      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['57'])).
% 1.60/1.77  thf('64', plain,
% 1.60/1.77      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['56', '58', '61', '62', '63'])).
% 1.60/1.77  thf('65', plain,
% 1.60/1.77      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['49', '64'])).
% 1.60/1.77  thf('66', plain,
% 1.60/1.77      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['56', '58', '61', '62', '63'])).
% 1.60/1.77  thf('67', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.77      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.77  thf('68', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.77  thf('69', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.77  thf('70', plain,
% 1.60/1.77      (![X17 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X17)
% 1.60/1.77          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.77          | ~ (v1_funct_1 @ X17)
% 1.60/1.77          | ~ (v1_relat_1 @ X17))),
% 1.60/1.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.77  thf('71', plain,
% 1.60/1.77      (![X30 : $i, X31 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.77  thf('72', plain,
% 1.60/1.77      (![X5 : $i, X6 : $i]:
% 1.60/1.77         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.77  thf('73', plain,
% 1.60/1.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['72'])).
% 1.60/1.77  thf('74', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.77         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.60/1.77      inference('sup+', [status(thm)], ['71', '73'])).
% 1.60/1.77  thf('75', plain,
% 1.60/1.77      (![X40 : $i]:
% 1.60/1.77         ((m1_subset_1 @ X40 @ 
% 1.60/1.77           (k1_zfmisc_1 @ 
% 1.60/1.77            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 1.60/1.77          | ~ (v1_funct_1 @ X40)
% 1.60/1.77          | ~ (v1_relat_1 @ X40))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.77  thf('76', plain,
% 1.60/1.77      (![X8 : $i, X9 : $i]:
% 1.60/1.77         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.77  thf('77', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | (r1_tarski @ X0 @ 
% 1.60/1.77             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.60/1.77      inference('sup-', [status(thm)], ['75', '76'])).
% 1.60/1.77  thf('78', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((r1_tarski @ X0 @ k1_xboole_0)
% 1.60/1.77          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('sup+', [status(thm)], ['74', '77'])).
% 1.60/1.77  thf(t3_xboole_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.60/1.77  thf('79', plain,
% 1.60/1.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.60/1.77  thf('80', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.77          | ((X0) = (k1_xboole_0)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['78', '79'])).
% 1.60/1.77  thf('81', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.60/1.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.60/1.77      inference('sup+', [status(thm)], ['70', '80'])).
% 1.60/1.77  thf('82', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 1.60/1.77      inference('sup-', [status(thm)], ['69', '81'])).
% 1.60/1.77  thf('83', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.60/1.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['82'])).
% 1.60/1.77  thf('84', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 1.60/1.77      inference('sup-', [status(thm)], ['68', '83'])).
% 1.60/1.77  thf('85', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 1.60/1.77          | ~ (v2_funct_1 @ X0)
% 1.60/1.77          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['84'])).
% 1.60/1.77  thf('86', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ sk_B @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ sk_C)
% 1.60/1.77          | ~ (v1_funct_1 @ sk_C)
% 1.60/1.77          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.60/1.77          | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.77      inference('sup+', [status(thm)], ['67', '85'])).
% 1.60/1.77  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.77  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('90', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 1.60/1.77      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.60/1.77  thf('91', plain,
% 1.60/1.77      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.77      inference('sup-', [status(thm)], ['13', '14'])).
% 1.60/1.77  thf('92', plain,
% 1.60/1.77      ((((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.60/1.77        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.60/1.77      inference('sup-', [status(thm)], ['90', '91'])).
% 1.60/1.77  thf('93', plain,
% 1.60/1.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.77      inference('demod', [status(thm)], ['19', '22'])).
% 1.60/1.77  thf('94', plain,
% 1.60/1.77      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['92', '93'])).
% 1.60/1.77  thf('95', plain,
% 1.60/1.77      (((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.60/1.77         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup+', [status(thm)], ['66', '94'])).
% 1.60/1.77  thf('96', plain,
% 1.60/1.77      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['56', '58', '61', '62', '63'])).
% 1.60/1.77  thf('97', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.60/1.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.77  thf('98', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.60/1.77      inference('simplify', [status(thm)], ['97'])).
% 1.60/1.77  thf('99', plain,
% 1.60/1.77      (![X8 : $i, X10 : $i]:
% 1.60/1.77         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.77  thf('100', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['98', '99'])).
% 1.60/1.77  thf('101', plain,
% 1.60/1.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['72'])).
% 1.60/1.77  thf(cc1_funct_2, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.77       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.60/1.77         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.60/1.77  thf('102', plain,
% 1.60/1.77      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.60/1.77         (~ (v1_funct_1 @ X27)
% 1.60/1.77          | ~ (v1_partfun1 @ X27 @ X28)
% 1.60/1.77          | (v1_funct_2 @ X27 @ X28 @ X29)
% 1.60/1.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.60/1.77      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.60/1.77  thf('103', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.60/1.77          | (v1_funct_2 @ X1 @ k1_xboole_0 @ X0)
% 1.60/1.77          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 1.60/1.77          | ~ (v1_funct_1 @ X1))),
% 1.60/1.77      inference('sup-', [status(thm)], ['101', '102'])).
% 1.60/1.77  thf('104', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_funct_1 @ k1_xboole_0)
% 1.60/1.77          | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 1.60/1.77          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['100', '103'])).
% 1.60/1.77  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('106', plain,
% 1.60/1.77      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.77  thf(cc3_funct_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.77       ( ![B:$i]:
% 1.60/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 1.60/1.77  thf('107', plain,
% 1.60/1.77      (![X14 : $i, X15 : $i]:
% 1.60/1.77         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.60/1.77          | (v1_funct_1 @ X14)
% 1.60/1.77          | ~ (v1_funct_1 @ X15)
% 1.60/1.77          | ~ (v1_relat_1 @ X15))),
% 1.60/1.77      inference('cnf', [status(esa)], [cc3_funct_1])).
% 1.60/1.77  thf('108', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | (v1_funct_1 @ k1_xboole_0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['106', '107'])).
% 1.60/1.77  thf('109', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.77      inference('sup-', [status(thm)], ['105', '108'])).
% 1.60/1.77  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.77  thf('111', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.60/1.77      inference('demod', [status(thm)], ['109', '110'])).
% 1.60/1.77  thf('112', plain,
% 1.60/1.77      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['57'])).
% 1.60/1.77  thf(dt_k6_partfun1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( m1_subset_1 @
% 1.60/1.77         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.60/1.77       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.60/1.77  thf('113', plain,
% 1.60/1.77      (![X39 : $i]:
% 1.60/1.77         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 1.60/1.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.60/1.77  thf('114', plain,
% 1.60/1.77      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.60/1.77      inference('sup+', [status(thm)], ['112', '113'])).
% 1.60/1.77  thf('115', plain,
% 1.60/1.77      (![X8 : $i, X9 : $i]:
% 1.60/1.77         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.77  thf('116', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 1.60/1.77      inference('sup-', [status(thm)], ['114', '115'])).
% 1.60/1.77  thf('117', plain,
% 1.60/1.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 1.60/1.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.60/1.77  thf('118', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['116', '117'])).
% 1.60/1.77  thf('119', plain, (![X38 : $i]: (v1_partfun1 @ (k6_partfun1 @ X38) @ X38)),
% 1.60/1.77      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.60/1.77  thf('120', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.60/1.77      inference('sup+', [status(thm)], ['118', '119'])).
% 1.60/1.77  thf('121', plain,
% 1.60/1.77      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.60/1.77      inference('demod', [status(thm)], ['104', '111', '120'])).
% 1.60/1.77  thf('122', plain,
% 1.60/1.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.60/1.77         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.60/1.77          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 1.60/1.77          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.60/1.77  thf('123', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.60/1.77          | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['121', '122'])).
% 1.60/1.77  thf('124', plain,
% 1.60/1.77      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.77  thf('125', plain,
% 1.60/1.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.77         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.60/1.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.60/1.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.77  thf('126', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['124', '125'])).
% 1.60/1.77  thf('127', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.60/1.77          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.60/1.77      inference('demod', [status(thm)], ['123', '126'])).
% 1.60/1.77  thf('128', plain,
% 1.60/1.77      (![X30 : $i, X31 : $i]:
% 1.60/1.77         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.77  thf('129', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 1.60/1.77      inference('simplify', [status(thm)], ['128'])).
% 1.60/1.77  thf('130', plain,
% 1.60/1.77      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.77  thf('131', plain,
% 1.60/1.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.60/1.77         (~ (zip_tseitin_0 @ X35 @ X36)
% 1.60/1.77          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 1.60/1.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.77  thf('132', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.60/1.77      inference('sup-', [status(thm)], ['130', '131'])).
% 1.60/1.77  thf('133', plain,
% 1.60/1.77      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.60/1.77      inference('sup-', [status(thm)], ['129', '132'])).
% 1.60/1.77  thf('134', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.60/1.77      inference('demod', [status(thm)], ['127', '133'])).
% 1.60/1.77  thf('135', plain,
% 1.60/1.77      (((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.60/1.77         | ((sk_A) = (k1_xboole_0))))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['95', '96', '134'])).
% 1.60/1.77  thf('136', plain,
% 1.60/1.77      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['49', '64'])).
% 1.60/1.77  thf('137', plain,
% 1.60/1.77      (((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 1.60/1.77         | ((sk_A) = (k1_xboole_0))))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['135', '136'])).
% 1.60/1.77  thf('138', plain,
% 1.60/1.77      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.60/1.77      inference('demod', [status(thm)], ['104', '111', '120'])).
% 1.60/1.77  thf('139', plain,
% 1.60/1.77      ((((sk_A) = (k1_xboole_0)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['137', '138'])).
% 1.60/1.77  thf('140', plain,
% 1.60/1.77      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.77  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.77      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.77  thf('142', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_funct_1 @ X0)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.60/1.77             (k1_relat_1 @ X0)))),
% 1.60/1.77      inference('simplify', [status(thm)], ['35'])).
% 1.60/1.77  thf('143', plain,
% 1.60/1.77      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.77        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.77        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.77      inference('sup+', [status(thm)], ['141', '142'])).
% 1.60/1.77  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.77  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('147', plain,
% 1.60/1.77      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.60/1.77      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 1.60/1.77  thf('148', plain,
% 1.60/1.77      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('sup+', [status(thm)], ['140', '147'])).
% 1.60/1.77  thf('149', plain,
% 1.60/1.77      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['56', '58', '61', '62', '63'])).
% 1.60/1.77  thf('150', plain,
% 1.60/1.77      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['56', '58', '61', '62', '63'])).
% 1.60/1.77  thf('151', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.60/1.77      inference('demod', [status(thm)], ['127', '133'])).
% 1.60/1.77  thf('152', plain,
% 1.60/1.77      (((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ k1_xboole_0))
% 1.60/1.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.77      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 1.60/1.77  thf('153', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.60/1.77      inference('demod', [status(thm)], ['65', '139', '152'])).
% 1.60/1.77  thf('154', plain,
% 1.60/1.77      (~
% 1.60/1.77       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.60/1.77       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.60/1.77       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.77      inference('split', [status(esa)], ['0'])).
% 1.60/1.77  thf('155', plain,
% 1.60/1.77      (~
% 1.60/1.77       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.77      inference('sat_resolution*', [status(thm)], ['10', '153', '154'])).
% 1.60/1.77  thf('156', plain,
% 1.60/1.77      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.77      inference('simpl_trail', [status(thm)], ['1', '155'])).
% 1.60/1.77  thf('157', plain,
% 1.60/1.77      (![X17 : $i]:
% 1.60/1.77         (~ (v2_funct_1 @ X17)
% 1.60/1.77          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.77          | ~ (v1_funct_1 @ X17)
% 1.60/1.77          | ~ (v1_relat_1 @ X17))),
% 1.60/1.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.77  thf('158', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.77      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.77  thf('159', plain,
% 1.60/1.77      (![X16 : $i]:
% 1.60/1.77         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.60/1.77          | ~ (v1_funct_1 @ X16)
% 1.60/1.77          | ~ (v1_relat_1 @ X16))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('160', plain,
% 1.60/1.78      (![X16 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.60/1.78          | ~ (v1_funct_1 @ X16)
% 1.60/1.78          | ~ (v1_relat_1 @ X16))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('161', plain,
% 1.60/1.78      (![X17 : $i]:
% 1.60/1.78         (~ (v2_funct_1 @ X17)
% 1.60/1.78          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.78          | ~ (v1_funct_1 @ X17)
% 1.60/1.78          | ~ (v1_relat_1 @ X17))),
% 1.60/1.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.78  thf('162', plain,
% 1.60/1.78      (![X40 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X40 @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 1.60/1.78          | ~ (v1_funct_1 @ X40)
% 1.60/1.78          | ~ (v1_relat_1 @ X40))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('163', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.60/1.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['161', '162'])).
% 1.60/1.78  thf('164', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ 
% 1.60/1.78              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.60/1.78               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['160', '163'])).
% 1.60/1.78  thf('165', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['164'])).
% 1.60/1.78  thf('166', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ 
% 1.60/1.78              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.60/1.78               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['159', '165'])).
% 1.60/1.78  thf('167', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['166'])).
% 1.60/1.78  thf('168', plain,
% 1.60/1.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ 
% 1.60/1.78          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['158', '167'])).
% 1.60/1.78  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.78  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('172', plain,
% 1.60/1.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78        (k1_zfmisc_1 @ 
% 1.60/1.78         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.60/1.78  thf('173', plain,
% 1.60/1.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['157', '172'])).
% 1.60/1.78  thf('174', plain,
% 1.60/1.78      (![X17 : $i]:
% 1.60/1.78         (~ (v2_funct_1 @ X17)
% 1.60/1.78          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.60/1.78          | ~ (v1_funct_1 @ X17)
% 1.60/1.78          | ~ (v1_relat_1 @ X17))),
% 1.60/1.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.78  thf('175', plain,
% 1.60/1.78      (![X16 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.60/1.78          | ~ (v1_funct_1 @ X16)
% 1.60/1.78          | ~ (v1_relat_1 @ X16))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('176', plain,
% 1.60/1.78      (![X16 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 1.60/1.78          | ~ (v1_funct_1 @ X16)
% 1.60/1.78          | ~ (v1_relat_1 @ X16))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('177', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.60/1.78      inference('sup+', [status(thm)], ['71', '73'])).
% 1.60/1.78  thf('178', plain,
% 1.60/1.78      (![X40 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X40 @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 1.60/1.78          | ~ (v1_funct_1 @ X40)
% 1.60/1.78          | ~ (v1_relat_1 @ X40))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('179', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.60/1.78          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0))),
% 1.60/1.78      inference('sup+', [status(thm)], ['177', '178'])).
% 1.60/1.78  thf('180', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.60/1.78      inference('sup+', [status(thm)], ['71', '73'])).
% 1.60/1.78  thf('181', plain,
% 1.60/1.78      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['13', '14'])).
% 1.60/1.78  thf('182', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.60/1.78          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['180', '181'])).
% 1.60/1.78  thf('183', plain,
% 1.60/1.78      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['19', '22'])).
% 1.60/1.78  thf('184', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.60/1.78          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['182', '183'])).
% 1.60/1.78  thf('185', plain,
% 1.60/1.78      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('split', [status(esa)], ['0'])).
% 1.60/1.78  thf('186', plain,
% 1.60/1.78      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.60/1.78         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['184', '185'])).
% 1.60/1.78  thf('187', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.60/1.78           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['179', '186'])).
% 1.60/1.78  thf('188', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (v1_relat_1 @ sk_C)
% 1.60/1.78           | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78           | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.60/1.78           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['176', '187'])).
% 1.60/1.78  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.78  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('191', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (((sk_A) = (k1_relat_1 @ sk_C))
% 1.60/1.78           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['188', '189', '190'])).
% 1.60/1.78  thf('192', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (v1_relat_1 @ sk_C)
% 1.60/1.78           | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.60/1.78           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['175', '191'])).
% 1.60/1.78  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.78  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('195', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.60/1.78           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['192', '193', '194'])).
% 1.60/1.78  thf('196', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 1.60/1.78           | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78           | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78           | ~ (v2_funct_1 @ sk_C)
% 1.60/1.78           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup+', [status(thm)], ['174', '195'])).
% 1.60/1.78  thf('197', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.78      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.78  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.78  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('201', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['196', '197', '198', '199', '200'])).
% 1.60/1.78  thf('202', plain,
% 1.60/1.78      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['13', '14'])).
% 1.60/1.78  thf('203', plain,
% 1.60/1.78      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['201', '202'])).
% 1.60/1.78  thf('204', plain,
% 1.60/1.78      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['19', '22'])).
% 1.60/1.78  thf('205', plain,
% 1.60/1.78      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('clc', [status(thm)], ['203', '204'])).
% 1.60/1.78  thf('206', plain,
% 1.60/1.78      (~
% 1.60/1.78       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['10', '153', '154'])).
% 1.60/1.78  thf('207', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['205', '206'])).
% 1.60/1.78  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.78  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('211', plain,
% 1.60/1.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['173', '207', '208', '209', '210'])).
% 1.60/1.78  thf('212', plain, ($false), inference('demod', [status(thm)], ['156', '211'])).
% 1.60/1.78  
% 1.60/1.78  % SZS output end Refutation
% 1.60/1.78  
% 1.60/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
