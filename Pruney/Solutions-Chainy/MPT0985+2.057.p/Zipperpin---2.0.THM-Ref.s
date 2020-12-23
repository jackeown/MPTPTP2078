%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIrcxXt6C3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:34 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  224 (2222 expanded)
%              Number of leaves         :   45 ( 675 expanded)
%              Depth                    :   24
%              Number of atoms          : 1839 (33708 expanded)
%              Number of equality atoms :   89 (1424 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ( ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A_1
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
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A_1 )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
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
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['11','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ),
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
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A_1 @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('62',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['49','62'])).

thf('64',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('65',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['65','66'])).

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
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('71',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('72',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X38: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X38 ) @ X38 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('80',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('81',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('82',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X28 )
      | ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(rc2_funct_1,axiom,(
    ? [A: $i] :
      ( ( v2_funct_1 @ A )
      & ( v1_funct_1 @ A )
      & ( v1_relat_1 @ A ) ) )).

thf('84',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc2_funct_1])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc2_funct_1])).

thf('90',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('98',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','100','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ( v1_funct_2 @ X41 @ ( k1_relat_1 @ X41 ) @ X42 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('111',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('112',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('113',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','114'])).

thf('116',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('117',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','118'])).

thf('120',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('121',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['67','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['64','123'])).

thf('125',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('126',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ k1_xboole_0 )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('129',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('130',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('133',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['127','128','131','132'])).

thf('134',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('135',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('136',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['124','133','134','135','136'])).

thf('138',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['63','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','138','139'])).

thf('141',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('143',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('144',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('145',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('147',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['143','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['142','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('161',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('162',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['160','162'])).

thf('164',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A_1
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('169',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A_1
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('171',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('172',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A_1
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','138','139'])).

thf('174',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['172','173'])).

thf('175',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['169','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['159','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['141','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIrcxXt6C3
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.25/2.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.25/2.48  % Solved by: fo/fo7.sh
% 2.25/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.48  % done 2282 iterations in 2.019s
% 2.25/2.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.25/2.48  % SZS output start Refutation
% 2.25/2.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.25/2.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.25/2.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.25/2.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.25/2.48  thf(sk_A_1_type, type, sk_A_1: $i).
% 2.25/2.48  thf(sk_C_type, type, sk_C: $i).
% 2.25/2.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.25/2.48  thf(sk_B_type, type, sk_B: $i).
% 2.25/2.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.25/2.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.25/2.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.25/2.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.25/2.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.25/2.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.25/2.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.25/2.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.25/2.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.25/2.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.25/2.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.25/2.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.25/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.25/2.48  thf(t31_funct_2, conjecture,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.48       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.25/2.48         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.25/2.48           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.25/2.48           ( m1_subset_1 @
% 2.25/2.48             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.25/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.48    (~( ![A:$i,B:$i,C:$i]:
% 2.25/2.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.48          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.25/2.48            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.25/2.48              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.25/2.48              ( m1_subset_1 @
% 2.25/2.48                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.25/2.48    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.25/2.48  thf('0', plain,
% 2.25/2.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.48        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)
% 2.25/2.48        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('1', plain,
% 2.25/2.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 2.25/2.48         <= (~
% 2.25/2.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf('2', plain,
% 2.25/2.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf(cc1_relset_1, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( v1_relat_1 @ C ) ))).
% 2.25/2.48  thf('3', plain,
% 2.25/2.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.48         ((v1_relat_1 @ X18)
% 2.25/2.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.25/2.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.25/2.48  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.48      inference('sup-', [status(thm)], ['2', '3'])).
% 2.25/2.48  thf(dt_k2_funct_1, axiom,
% 2.25/2.48    (![A:$i]:
% 2.25/2.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.25/2.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.25/2.48  thf('5', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('6', plain,
% 2.25/2.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf('7', plain,
% 2.25/2.48      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.25/2.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['5', '6'])).
% 2.25/2.48  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('9', plain,
% 2.25/2.48      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.25/2.48      inference('demod', [status(thm)], ['7', '8'])).
% 2.25/2.48  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['4', '9'])).
% 2.25/2.48  thf('11', plain,
% 2.25/2.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf(d1_funct_2, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.25/2.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.25/2.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.25/2.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.25/2.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.25/2.48  thf(zf_stmt_1, axiom,
% 2.25/2.48    (![B:$i,A:$i]:
% 2.25/2.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.25/2.48       ( zip_tseitin_0 @ B @ A ) ))).
% 2.25/2.48  thf('12', plain,
% 2.25/2.48      (![X30 : $i, X31 : $i]:
% 2.25/2.48         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.25/2.48  thf('13', plain,
% 2.25/2.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.25/2.48  thf(zf_stmt_3, axiom,
% 2.25/2.48    (![C:$i,B:$i,A:$i]:
% 2.25/2.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.25/2.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.25/2.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.25/2.48  thf(zf_stmt_5, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.25/2.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.25/2.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.25/2.48  thf('14', plain,
% 2.25/2.48      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.25/2.48         (~ (zip_tseitin_0 @ X35 @ X36)
% 2.25/2.48          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 2.25/2.48          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.25/2.48  thf('15', plain,
% 2.25/2.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 2.25/2.48        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['13', '14'])).
% 2.25/2.48  thf('16', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['12', '15'])).
% 2.25/2.48  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('18', plain,
% 2.25/2.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.25/2.48         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 2.25/2.48          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 2.25/2.48          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.25/2.48  thf('19', plain,
% 2.25/2.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 2.25/2.48        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['17', '18'])).
% 2.25/2.48  thf('20', plain,
% 2.25/2.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf(redefinition_k1_relset_1, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.25/2.48  thf('21', plain,
% 2.25/2.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.25/2.48         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.25/2.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.25/2.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.25/2.48  thf('22', plain,
% 2.25/2.48      (((k1_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.25/2.48      inference('sup-', [status(thm)], ['20', '21'])).
% 2.25/2.48  thf('23', plain,
% 2.25/2.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 2.25/2.48        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('demod', [status(thm)], ['19', '22'])).
% 2.25/2.48  thf('24', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)) | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['16', '23'])).
% 2.25/2.48  thf(t55_funct_1, axiom,
% 2.25/2.48    (![A:$i]:
% 2.25/2.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.48       ( ( v2_funct_1 @ A ) =>
% 2.25/2.48         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.25/2.48           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.25/2.48  thf('25', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf('26', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('27', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('28', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf(t3_funct_2, axiom,
% 2.25/2.48    (![A:$i]:
% 2.25/2.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.48       ( ( v1_funct_1 @ A ) & 
% 2.25/2.48         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.25/2.48         ( m1_subset_1 @
% 2.25/2.48           A @ 
% 2.25/2.48           ( k1_zfmisc_1 @
% 2.25/2.48             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.25/2.48  thf('29', plain,
% 2.25/2.48      (![X40 : $i]:
% 2.25/2.48         ((v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))
% 2.25/2.48          | ~ (v1_funct_1 @ X40)
% 2.25/2.48          | ~ (v1_relat_1 @ X40))),
% 2.25/2.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.25/2.48  thf('30', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['28', '29'])).
% 2.25/2.48  thf('31', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['27', '30'])).
% 2.25/2.48  thf('32', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['31'])).
% 2.25/2.48  thf('33', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['26', '32'])).
% 2.25/2.48  thf('34', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['33'])).
% 2.25/2.48  thf('35', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48           (k1_relat_1 @ X0))
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0))),
% 2.25/2.48      inference('sup+', [status(thm)], ['25', '34'])).
% 2.25/2.48  thf('36', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.25/2.48             (k1_relat_1 @ X0)))),
% 2.25/2.48      inference('simplify', [status(thm)], ['35'])).
% 2.25/2.48  thf('37', plain,
% 2.25/2.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A_1)
% 2.25/2.48        | ((sk_B) = (k1_xboole_0))
% 2.25/2.48        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.48        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.48        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.48      inference('sup+', [status(thm)], ['24', '36'])).
% 2.25/2.48  thf('38', plain,
% 2.25/2.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf(redefinition_k2_relset_1, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.25/2.48  thf('39', plain,
% 2.25/2.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.25/2.48         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 2.25/2.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.25/2.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.25/2.48  thf('40', plain,
% 2.25/2.48      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.25/2.48      inference('sup-', [status(thm)], ['38', '39'])).
% 2.25/2.48  thf('41', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.25/2.48      inference('sup+', [status(thm)], ['40', '41'])).
% 2.25/2.48  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.48      inference('sup-', [status(thm)], ['2', '3'])).
% 2.25/2.48  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('46', plain,
% 2.25/2.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)
% 2.25/2.48        | ((sk_B) = (k1_xboole_0)))),
% 2.25/2.48      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 2.25/2.48  thf('47', plain,
% 2.25/2.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf('48', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.48  thf('49', plain,
% 2.25/2.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A_1))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['11', '48'])).
% 2.25/2.48  thf('50', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.48  thf('51', plain,
% 2.25/2.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf(t3_subset, axiom,
% 2.25/2.48    (![A:$i,B:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.25/2.48  thf('52', plain,
% 2.25/2.48      (![X8 : $i, X9 : $i]:
% 2.25/2.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.25/2.48      inference('cnf', [status(esa)], [t3_subset])).
% 2.25/2.48  thf('53', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))),
% 2.25/2.48      inference('sup-', [status(thm)], ['51', '52'])).
% 2.25/2.48  thf(d10_xboole_0, axiom,
% 2.25/2.48    (![A:$i,B:$i]:
% 2.25/2.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.25/2.48  thf('54', plain,
% 2.25/2.48      (![X0 : $i, X2 : $i]:
% 2.25/2.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.25/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.48  thf('55', plain,
% 2.25/2.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A_1 @ sk_B) @ sk_C)
% 2.25/2.48        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['53', '54'])).
% 2.25/2.48  thf('56', plain,
% 2.25/2.48      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A_1 @ k1_xboole_0) @ sk_C)
% 2.25/2.48         | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_C))))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['50', '55'])).
% 2.25/2.48  thf(t113_zfmisc_1, axiom,
% 2.25/2.48    (![A:$i,B:$i]:
% 2.25/2.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.25/2.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.25/2.48  thf('57', plain,
% 2.25/2.48      (![X5 : $i, X6 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 2.25/2.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.25/2.48  thf('58', plain,
% 2.25/2.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['57'])).
% 2.25/2.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.25/2.48  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.25/2.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.25/2.48  thf('60', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.48  thf('61', plain,
% 2.25/2.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['57'])).
% 2.25/2.48  thf('62', plain,
% 2.25/2.48      ((((k1_xboole_0) = (sk_C)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 2.25/2.48  thf('63', plain,
% 2.25/2.48      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A_1))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['49', '62'])).
% 2.25/2.48  thf('64', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf('65', plain,
% 2.25/2.48      ((((k1_xboole_0) = (sk_C)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 2.25/2.48  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('67', plain,
% 2.25/2.48      (((v2_funct_1 @ k1_xboole_0))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['65', '66'])).
% 2.25/2.48  thf('68', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('69', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('70', plain,
% 2.25/2.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['57'])).
% 2.25/2.48  thf(dt_k6_partfun1, axiom,
% 2.25/2.48    (![A:$i]:
% 2.25/2.48     ( ( m1_subset_1 @
% 2.25/2.48         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.25/2.48       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.25/2.48  thf('71', plain,
% 2.25/2.48      (![X39 : $i]:
% 2.25/2.48         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 2.25/2.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.25/2.48  thf('72', plain,
% 2.25/2.48      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup+', [status(thm)], ['70', '71'])).
% 2.25/2.48  thf('73', plain,
% 2.25/2.48      (![X8 : $i, X9 : $i]:
% 2.25/2.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.25/2.48      inference('cnf', [status(esa)], [t3_subset])).
% 2.25/2.48  thf('74', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['72', '73'])).
% 2.25/2.48  thf('75', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.25/2.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.25/2.48  thf('76', plain,
% 2.25/2.48      (![X0 : $i, X2 : $i]:
% 2.25/2.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.25/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.48  thf('77', plain,
% 2.25/2.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['75', '76'])).
% 2.25/2.48  thf('78', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['74', '77'])).
% 2.25/2.48  thf('79', plain, (![X38 : $i]: (v1_partfun1 @ (k6_partfun1 @ X38) @ X38)),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.25/2.48  thf('80', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 2.25/2.48      inference('sup+', [status(thm)], ['78', '79'])).
% 2.25/2.48  thf(t4_subset_1, axiom,
% 2.25/2.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.25/2.48  thf('81', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf(cc1_funct_2, axiom,
% 2.25/2.48    (![A:$i,B:$i,C:$i]:
% 2.25/2.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.48       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 2.25/2.48         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 2.25/2.48  thf('82', plain,
% 2.25/2.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.25/2.48         (~ (v1_funct_1 @ X27)
% 2.25/2.48          | ~ (v1_partfun1 @ X27 @ X28)
% 2.25/2.48          | (v1_funct_2 @ X27 @ X28 @ X29)
% 2.25/2.48          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 2.25/2.48      inference('cnf', [status(esa)], [cc1_funct_2])).
% 2.25/2.48  thf('83', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 2.25/2.48          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 2.25/2.48          | ~ (v1_funct_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['81', '82'])).
% 2.25/2.48  thf(rc2_funct_1, axiom,
% 2.25/2.48    (?[A:$i]: ( ( v2_funct_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ))).
% 2.25/2.48  thf('84', plain, ((v1_funct_1 @ sk_A)),
% 2.25/2.48      inference('cnf', [status(esa)], [rc2_funct_1])).
% 2.25/2.48  thf('85', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf(cc3_funct_1, axiom,
% 2.25/2.48    (![A:$i]:
% 2.25/2.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.48       ( ![B:$i]:
% 2.25/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 2.25/2.48  thf('86', plain,
% 2.25/2.48      (![X14 : $i, X15 : $i]:
% 2.25/2.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 2.25/2.48          | (v1_funct_1 @ X14)
% 2.25/2.48          | ~ (v1_funct_1 @ X15)
% 2.25/2.48          | ~ (v1_relat_1 @ X15))),
% 2.25/2.48      inference('cnf', [status(esa)], [cc3_funct_1])).
% 2.25/2.48  thf('87', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | (v1_funct_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['85', '86'])).
% 2.25/2.48  thf('88', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_A))),
% 2.25/2.48      inference('sup-', [status(thm)], ['84', '87'])).
% 2.25/2.48  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 2.25/2.48      inference('cnf', [status(esa)], [rc2_funct_1])).
% 2.25/2.48  thf('90', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.25/2.48      inference('demod', [status(thm)], ['88', '89'])).
% 2.25/2.48  thf('91', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 2.25/2.48          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 2.25/2.48      inference('demod', [status(thm)], ['83', '90'])).
% 2.25/2.48  thf('92', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['80', '91'])).
% 2.25/2.48  thf('93', plain,
% 2.25/2.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.25/2.48         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 2.25/2.48          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 2.25/2.48          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.25/2.48  thf('94', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.25/2.48          | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['92', '93'])).
% 2.25/2.48  thf('95', plain,
% 2.25/2.48      (![X30 : $i, X31 : $i]:
% 2.25/2.48         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.25/2.48  thf('96', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 2.25/2.48      inference('simplify', [status(thm)], ['95'])).
% 2.25/2.48  thf('97', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf('98', plain,
% 2.25/2.48      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.25/2.48         (~ (zip_tseitin_0 @ X35 @ X36)
% 2.25/2.48          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 2.25/2.48          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.25/2.48  thf('99', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['97', '98'])).
% 2.25/2.48  thf('100', plain,
% 2.25/2.48      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['96', '99'])).
% 2.25/2.48  thf('101', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf('102', plain,
% 2.25/2.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.25/2.48         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.25/2.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.25/2.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.25/2.48  thf('103', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['101', '102'])).
% 2.25/2.48  thf('104', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.25/2.48      inference('demod', [status(thm)], ['94', '100', '103'])).
% 2.25/2.48  thf('105', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf(t4_funct_2, axiom,
% 2.25/2.48    (![A:$i,B:$i]:
% 2.25/2.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.25/2.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.25/2.48         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 2.25/2.48           ( m1_subset_1 @
% 2.25/2.48             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 2.25/2.48  thf('106', plain,
% 2.25/2.48      (![X41 : $i, X42 : $i]:
% 2.25/2.48         (~ (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 2.25/2.48          | (v1_funct_2 @ X41 @ (k1_relat_1 @ X41) @ X42)
% 2.25/2.48          | ~ (v1_funct_1 @ X41)
% 2.25/2.48          | ~ (v1_relat_1 @ X41))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.25/2.48  thf('107', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['105', '106'])).
% 2.25/2.48  thf('108', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48             (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | ~ (v2_funct_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['104', '107'])).
% 2.25/2.48  thf('109', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.25/2.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.25/2.48  thf('110', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.25/2.48      inference('demod', [status(thm)], ['88', '89'])).
% 2.25/2.48  thf('111', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf('112', plain,
% 2.25/2.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.48         ((v1_relat_1 @ X18)
% 2.25/2.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.25/2.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.25/2.48  thf('113', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['111', '112'])).
% 2.25/2.48  thf('114', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48           (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | ~ (v2_funct_1 @ k1_xboole_0))),
% 2.25/2.48      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 2.25/2.48  thf('115', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v2_funct_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48             (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['69', '114'])).
% 2.25/2.48  thf('116', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['111', '112'])).
% 2.25/2.48  thf('117', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.25/2.48      inference('demod', [status(thm)], ['88', '89'])).
% 2.25/2.48  thf('118', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48             (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0))),
% 2.25/2.48      inference('demod', [status(thm)], ['115', '116', '117'])).
% 2.25/2.48  thf('119', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ k1_xboole_0)
% 2.25/2.48          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.25/2.48          | (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48             (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['68', '118'])).
% 2.25/2.48  thf('120', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['111', '112'])).
% 2.25/2.48  thf('121', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.25/2.48      inference('demod', [status(thm)], ['88', '89'])).
% 2.25/2.48  thf('122', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48           (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ k1_xboole_0))),
% 2.25/2.48      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.25/2.48  thf('123', plain,
% 2.25/2.48      ((![X0 : $i]:
% 2.25/2.48          (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48           (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ X0))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['67', '122'])).
% 2.25/2.48  thf('124', plain,
% 2.25/2.48      ((![X0 : $i]:
% 2.25/2.48          ((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.25/2.48            (k2_relat_1 @ k1_xboole_0) @ X0)
% 2.25/2.48           | ~ (v1_relat_1 @ k1_xboole_0)
% 2.25/2.48           | ~ (v1_funct_1 @ k1_xboole_0)
% 2.25/2.48           | ~ (v2_funct_1 @ k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['64', '123'])).
% 2.25/2.48  thf('125', plain,
% 2.25/2.48      ((((k1_xboole_0) = (sk_C)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 2.25/2.48  thf('126', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('127', plain,
% 2.25/2.48      ((((k2_relset_1 @ sk_A_1 @ sk_B @ k1_xboole_0) = (sk_B)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['125', '126'])).
% 2.25/2.48  thf('128', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.48  thf('129', plain,
% 2.25/2.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 2.25/2.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.25/2.48  thf('130', plain,
% 2.25/2.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.25/2.48         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 2.25/2.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.25/2.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.25/2.48  thf('131', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i]:
% 2.25/2.48         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 2.25/2.48      inference('sup-', [status(thm)], ['129', '130'])).
% 2.25/2.48  thf('132', plain,
% 2.25/2.48      ((((sk_B) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.48  thf('133', plain,
% 2.25/2.48      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['127', '128', '131', '132'])).
% 2.25/2.48  thf('134', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.25/2.48      inference('sup-', [status(thm)], ['111', '112'])).
% 2.25/2.48  thf('135', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.25/2.48      inference('demod', [status(thm)], ['88', '89'])).
% 2.25/2.48  thf('136', plain,
% 2.25/2.48      (((v2_funct_1 @ k1_xboole_0))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['65', '66'])).
% 2.25/2.48  thf('137', plain,
% 2.25/2.48      ((![X0 : $i]:
% 2.25/2.48          (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ X0))
% 2.25/2.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['124', '133', '134', '135', '136'])).
% 2.25/2.48  thf('138', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))),
% 2.25/2.48      inference('demod', [status(thm)], ['63', '137'])).
% 2.25/2.48  thf('139', plain,
% 2.25/2.48      (~
% 2.25/2.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))) | 
% 2.25/2.48       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)) | 
% 2.25/2.48       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf('140', plain,
% 2.25/2.48      (~
% 2.25/2.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 2.25/2.48      inference('sat_resolution*', [status(thm)], ['10', '138', '139'])).
% 2.25/2.48  thf('141', plain,
% 2.25/2.48      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('simpl_trail', [status(thm)], ['1', '140'])).
% 2.25/2.48  thf('142', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.25/2.48      inference('sup+', [status(thm)], ['40', '41'])).
% 2.25/2.48  thf('143', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf('144', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('145', plain,
% 2.25/2.48      (![X16 : $i]:
% 2.25/2.48         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 2.25/2.48          | ~ (v1_funct_1 @ X16)
% 2.25/2.48          | ~ (v1_relat_1 @ X16))),
% 2.25/2.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.25/2.48  thf('146', plain,
% 2.25/2.48      (![X17 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X17)
% 2.25/2.48          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 2.25/2.48          | ~ (v1_funct_1 @ X17)
% 2.25/2.48          | ~ (v1_relat_1 @ X17))),
% 2.25/2.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.48  thf('147', plain,
% 2.25/2.48      (![X40 : $i]:
% 2.25/2.48         ((m1_subset_1 @ X40 @ 
% 2.25/2.48           (k1_zfmisc_1 @ 
% 2.25/2.48            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 2.25/2.48          | ~ (v1_funct_1 @ X40)
% 2.25/2.48          | ~ (v1_relat_1 @ X40))),
% 2.25/2.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.25/2.48  thf('148', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48           (k1_zfmisc_1 @ 
% 2.25/2.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['146', '147'])).
% 2.25/2.48  thf('149', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48             (k1_zfmisc_1 @ 
% 2.25/2.48              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.25/2.48               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['145', '148'])).
% 2.25/2.48  thf('150', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48           (k1_zfmisc_1 @ 
% 2.25/2.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['149'])).
% 2.25/2.48  thf('151', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48             (k1_zfmisc_1 @ 
% 2.25/2.48              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.25/2.48               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['144', '150'])).
% 2.25/2.48  thf('152', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48           (k1_zfmisc_1 @ 
% 2.25/2.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['151'])).
% 2.25/2.48  thf('153', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v2_funct_1 @ X0))),
% 2.25/2.48      inference('sup+', [status(thm)], ['143', '152'])).
% 2.25/2.48  thf('154', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (~ (v2_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_funct_1 @ X0)
% 2.25/2.48          | ~ (v1_relat_1 @ X0)
% 2.25/2.48          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.25/2.48             (k1_zfmisc_1 @ 
% 2.25/2.48              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 2.25/2.48      inference('simplify', [status(thm)], ['153'])).
% 2.25/2.48  thf('155', plain,
% 2.25/2.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 2.25/2.48        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.48        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.48        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.48      inference('sup+', [status(thm)], ['142', '154'])).
% 2.25/2.48  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.48      inference('sup-', [status(thm)], ['2', '3'])).
% 2.25/2.48  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.48  thf('159', plain,
% 2.25/2.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 2.25/2.48      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 2.25/2.48  thf('160', plain,
% 2.25/2.48      (![X30 : $i, X31 : $i]:
% 2.25/2.48         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 2.25/2.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.25/2.48  thf('161', plain,
% 2.25/2.48      (![X5 : $i, X6 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.25/2.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.25/2.48  thf('162', plain,
% 2.25/2.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.25/2.48      inference('simplify', [status(thm)], ['161'])).
% 2.25/2.48  thf('163', plain,
% 2.25/2.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.25/2.48      inference('sup+', [status(thm)], ['160', '162'])).
% 2.25/2.48  thf('164', plain,
% 2.25/2.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 2.25/2.48        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['13', '14'])).
% 2.25/2.48  thf('165', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.25/2.48          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1))),
% 2.25/2.48      inference('sup-', [status(thm)], ['163', '164'])).
% 2.25/2.48  thf('166', plain,
% 2.25/2.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 2.25/2.48        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('demod', [status(thm)], ['19', '22'])).
% 2.25/2.48  thf('167', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.25/2.48          | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['165', '166'])).
% 2.25/2.48  thf('168', plain,
% 2.25/2.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 2.25/2.48      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 2.25/2.48  thf('169', plain,
% 2.25/2.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.25/2.48        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('sup+', [status(thm)], ['167', '168'])).
% 2.25/2.48  thf('170', plain,
% 2.25/2.48      (![X0 : $i]:
% 2.25/2.48         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.25/2.48          | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('sup-', [status(thm)], ['165', '166'])).
% 2.25/2.48  thf('171', plain,
% 2.25/2.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 2.25/2.48         <= (~
% 2.25/2.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 2.25/2.48      inference('split', [status(esa)], ['0'])).
% 2.25/2.48  thf('172', plain,
% 2.25/2.48      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.25/2.48         | ((sk_A_1) = (k1_relat_1 @ sk_C))))
% 2.25/2.48         <= (~
% 2.25/2.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 2.25/2.48      inference('sup-', [status(thm)], ['170', '171'])).
% 2.25/2.48  thf('173', plain,
% 2.25/2.48      (~
% 2.25/2.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 2.25/2.48      inference('sat_resolution*', [status(thm)], ['10', '138', '139'])).
% 2.25/2.48  thf('174', plain,
% 2.25/2.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.25/2.48        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 2.25/2.48      inference('simpl_trail', [status(thm)], ['172', '173'])).
% 2.25/2.48  thf('175', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 2.25/2.48      inference('clc', [status(thm)], ['169', '174'])).
% 2.25/2.48  thf('176', plain,
% 2.25/2.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.25/2.48      inference('demod', [status(thm)], ['159', '175'])).
% 2.25/2.48  thf('177', plain, ($false), inference('demod', [status(thm)], ['141', '176'])).
% 2.25/2.48  
% 2.25/2.48  % SZS output end Refutation
% 2.25/2.48  
% 2.25/2.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
