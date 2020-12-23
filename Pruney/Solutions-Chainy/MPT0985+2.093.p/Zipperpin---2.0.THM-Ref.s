%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GEjfXBJvnD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:39 EST 2020

% Result     : Theorem 8.98s
% Output     : Refutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  236 (4522 expanded)
%              Number of leaves         :   46 (1345 expanded)
%              Depth                    :   28
%              Number of atoms          : 1936 (65882 expanded)
%              Number of equality atoms :  128 (3284 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X43: $i] :
      ( ( v1_funct_2 @ X43 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
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
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('62',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','62'])).

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('66',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('67',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('73',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('74',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('75',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','88'])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','62'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
        | ~ ( v2_funct_1 @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('96',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('97',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('100',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('109',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['105','111'])).

thf('113',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('118',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('122',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('124',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('125',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','112','115','122','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 != k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ( X39 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('130',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X38 @ k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('132',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('133',plain,(
    ! [X38: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X38 @ k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ! [X0: $i] : ( X0 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf('140',plain,
    ( ! [X0: $i] : ( X0 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf('141',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['105','111'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['63','139','140','141'])).

thf('143',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('144',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','142','143'])).

thf('145',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('147',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['146','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('157',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('164',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('167',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ X0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['162','174'])).

thf('176',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','142','143'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['185'])).

thf('187',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','186'])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['145','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GEjfXBJvnD
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 8.98/9.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.98/9.18  % Solved by: fo/fo7.sh
% 8.98/9.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.98/9.18  % done 5476 iterations in 8.705s
% 8.98/9.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.98/9.18  % SZS output start Refutation
% 8.98/9.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.98/9.18  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 8.98/9.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.98/9.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.98/9.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.98/9.18  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 8.98/9.18  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.98/9.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.98/9.18  thf(sk_A_type, type, sk_A: $i).
% 8.98/9.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.98/9.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 8.98/9.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.98/9.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.98/9.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 8.98/9.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.98/9.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.98/9.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.98/9.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.98/9.18  thf(sk_B_type, type, sk_B: $i).
% 8.98/9.18  thf(sk_C_type, type, sk_C: $i).
% 8.98/9.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.98/9.18  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.98/9.18  thf(t31_funct_2, conjecture,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.98/9.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.18       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 8.98/9.18         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 8.98/9.18           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 8.98/9.18           ( m1_subset_1 @
% 8.98/9.18             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 8.98/9.18  thf(zf_stmt_0, negated_conjecture,
% 8.98/9.18    (~( ![A:$i,B:$i,C:$i]:
% 8.98/9.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.98/9.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.18          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 8.98/9.18            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 8.98/9.18              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 8.98/9.18              ( m1_subset_1 @
% 8.98/9.18                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 8.98/9.18    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 8.98/9.18  thf('0', plain,
% 8.98/9.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 8.98/9.18        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 8.98/9.18        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('1', plain,
% 8.98/9.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf('2', plain,
% 8.98/9.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf(cc1_relset_1, axiom,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.18       ( v1_relat_1 @ C ) ))).
% 8.98/9.18  thf('3', plain,
% 8.98/9.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.98/9.18         ((v1_relat_1 @ X23)
% 8.98/9.18          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 8.98/9.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.98/9.18  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.18      inference('sup-', [status(thm)], ['2', '3'])).
% 8.98/9.18  thf(dt_k2_funct_1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.98/9.18       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 8.98/9.18         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 8.98/9.18  thf('5', plain,
% 8.98/9.18      (![X21 : $i]:
% 8.98/9.18         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 8.98/9.18          | ~ (v1_funct_1 @ X21)
% 8.98/9.18          | ~ (v1_relat_1 @ X21))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.98/9.18  thf('6', plain,
% 8.98/9.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 8.98/9.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf('7', plain,
% 8.98/9.18      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 8.98/9.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['5', '6'])).
% 8.98/9.18  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('9', plain,
% 8.98/9.18      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 8.98/9.18      inference('demod', [status(thm)], ['7', '8'])).
% 8.98/9.18  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['4', '9'])).
% 8.98/9.18  thf('11', plain,
% 8.98/9.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf(d1_funct_2, axiom,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.98/9.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 8.98/9.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 8.98/9.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.98/9.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 8.98/9.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 8.98/9.18  thf(zf_stmt_1, axiom,
% 8.98/9.18    (![B:$i,A:$i]:
% 8.98/9.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.98/9.18       ( zip_tseitin_0 @ B @ A ) ))).
% 8.98/9.18  thf('12', plain,
% 8.98/9.18      (![X32 : $i, X33 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.98/9.18  thf('13', plain,
% 8.98/9.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 8.98/9.18  thf(zf_stmt_3, axiom,
% 8.98/9.18    (![C:$i,B:$i,A:$i]:
% 8.98/9.18     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 8.98/9.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 8.98/9.18  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 8.98/9.18  thf(zf_stmt_5, axiom,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.18       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 8.98/9.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.98/9.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 8.98/9.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 8.98/9.18  thf('14', plain,
% 8.98/9.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.98/9.18         (~ (zip_tseitin_0 @ X37 @ X38)
% 8.98/9.18          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 8.98/9.18          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.98/9.18  thf('15', plain,
% 8.98/9.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 8.98/9.18      inference('sup-', [status(thm)], ['13', '14'])).
% 8.98/9.18  thf('16', plain,
% 8.98/9.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 8.98/9.18      inference('sup-', [status(thm)], ['12', '15'])).
% 8.98/9.18  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('18', plain,
% 8.98/9.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.98/9.18         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 8.98/9.18          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 8.98/9.18          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.98/9.18  thf('19', plain,
% 8.98/9.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 8.98/9.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['17', '18'])).
% 8.98/9.18  thf('20', plain,
% 8.98/9.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf(redefinition_k1_relset_1, axiom,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 8.98/9.18  thf('21', plain,
% 8.98/9.18      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.98/9.18         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 8.98/9.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.98/9.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.98/9.18  thf('22', plain,
% 8.98/9.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 8.98/9.18      inference('sup-', [status(thm)], ['20', '21'])).
% 8.98/9.18  thf('23', plain,
% 8.98/9.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('demod', [status(thm)], ['19', '22'])).
% 8.98/9.18  thf('24', plain,
% 8.98/9.18      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['16', '23'])).
% 8.98/9.18  thf(t55_funct_1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.98/9.18       ( ( v2_funct_1 @ A ) =>
% 8.98/9.18         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 8.98/9.18           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.98/9.18  thf('25', plain,
% 8.98/9.18      (![X22 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X22)
% 8.98/9.18          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 8.98/9.18          | ~ (v1_funct_1 @ X22)
% 8.98/9.18          | ~ (v1_relat_1 @ X22))),
% 8.98/9.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.98/9.18  thf('26', plain,
% 8.98/9.18      (![X21 : $i]:
% 8.98/9.18         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 8.98/9.18          | ~ (v1_funct_1 @ X21)
% 8.98/9.18          | ~ (v1_relat_1 @ X21))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.98/9.18  thf('27', plain,
% 8.98/9.18      (![X21 : $i]:
% 8.98/9.18         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 8.98/9.18          | ~ (v1_funct_1 @ X21)
% 8.98/9.18          | ~ (v1_relat_1 @ X21))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.98/9.18  thf('28', plain,
% 8.98/9.18      (![X22 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X22)
% 8.98/9.18          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 8.98/9.18          | ~ (v1_funct_1 @ X22)
% 8.98/9.18          | ~ (v1_relat_1 @ X22))),
% 8.98/9.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.98/9.18  thf(t3_funct_2, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.98/9.18       ( ( v1_funct_1 @ A ) & 
% 8.98/9.18         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 8.98/9.18         ( m1_subset_1 @
% 8.98/9.18           A @ 
% 8.98/9.18           ( k1_zfmisc_1 @
% 8.98/9.18             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 8.98/9.18  thf('29', plain,
% 8.98/9.18      (![X43 : $i]:
% 8.98/9.18         ((v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))
% 8.98/9.18          | ~ (v1_funct_1 @ X43)
% 8.98/9.18          | ~ (v1_relat_1 @ X43))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 8.98/9.18  thf('30', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 8.98/9.18      inference('sup+', [status(thm)], ['28', '29'])).
% 8.98/9.18  thf('31', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['27', '30'])).
% 8.98/9.18  thf('32', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['31'])).
% 8.98/9.18  thf('33', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['26', '32'])).
% 8.98/9.18  thf('34', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['33'])).
% 8.98/9.18  thf('35', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18           (k1_relat_1 @ X0))
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['25', '34'])).
% 8.98/9.18  thf('36', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 8.98/9.18             (k1_relat_1 @ X0)))),
% 8.98/9.18      inference('simplify', [status(thm)], ['35'])).
% 8.98/9.18  thf('37', plain,
% 8.98/9.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 8.98/9.18        | ((sk_B) = (k1_xboole_0))
% 8.98/9.18        | ~ (v1_relat_1 @ sk_C)
% 8.98/9.18        | ~ (v1_funct_1 @ sk_C)
% 8.98/9.18        | ~ (v2_funct_1 @ sk_C))),
% 8.98/9.18      inference('sup+', [status(thm)], ['24', '36'])).
% 8.98/9.18  thf('38', plain,
% 8.98/9.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf(redefinition_k2_relset_1, axiom,
% 8.98/9.18    (![A:$i,B:$i,C:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.98/9.18  thf('39', plain,
% 8.98/9.18      (![X29 : $i, X30 : $i, X31 : $i]:
% 8.98/9.18         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 8.98/9.18          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 8.98/9.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.98/9.18  thf('40', plain,
% 8.98/9.18      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 8.98/9.18      inference('sup-', [status(thm)], ['38', '39'])).
% 8.98/9.18  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.98/9.18      inference('sup+', [status(thm)], ['40', '41'])).
% 8.98/9.18  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.18      inference('sup-', [status(thm)], ['2', '3'])).
% 8.98/9.18  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('46', plain,
% 8.98/9.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 8.98/9.18        | ((sk_B) = (k1_xboole_0)))),
% 8.98/9.18      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 8.98/9.18  thf('47', plain,
% 8.98/9.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf('48', plain,
% 8.98/9.18      ((((sk_B) = (k1_xboole_0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['46', '47'])).
% 8.98/9.18  thf('49', plain,
% 8.98/9.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['11', '48'])).
% 8.98/9.18  thf('50', plain,
% 8.98/9.18      ((((sk_B) = (k1_xboole_0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['46', '47'])).
% 8.98/9.18  thf('51', plain,
% 8.98/9.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf(t3_subset, axiom,
% 8.98/9.18    (![A:$i,B:$i]:
% 8.98/9.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.98/9.18  thf('52', plain,
% 8.98/9.18      (![X9 : $i, X10 : $i]:
% 8.98/9.18         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_subset])).
% 8.98/9.18  thf('53', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 8.98/9.18      inference('sup-', [status(thm)], ['51', '52'])).
% 8.98/9.18  thf(d10_xboole_0, axiom,
% 8.98/9.18    (![A:$i,B:$i]:
% 8.98/9.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.98/9.18  thf('54', plain,
% 8.98/9.18      (![X0 : $i, X2 : $i]:
% 8.98/9.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.98/9.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.98/9.18  thf('55', plain,
% 8.98/9.18      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 8.98/9.18        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['53', '54'])).
% 8.98/9.18  thf('56', plain,
% 8.98/9.18      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 8.98/9.18         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['50', '55'])).
% 8.98/9.18  thf(t113_zfmisc_1, axiom,
% 8.98/9.18    (![A:$i,B:$i]:
% 8.98/9.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 8.98/9.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 8.98/9.18  thf('57', plain,
% 8.98/9.18      (![X6 : $i, X7 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.98/9.18  thf('58', plain,
% 8.98/9.18      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['57'])).
% 8.98/9.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.98/9.18  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 8.98/9.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.98/9.18  thf('60', plain,
% 8.98/9.18      ((((sk_B) = (k1_xboole_0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['46', '47'])).
% 8.98/9.18  thf('61', plain,
% 8.98/9.18      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['57'])).
% 8.98/9.18  thf('62', plain,
% 8.98/9.18      ((((k1_xboole_0) = (sk_C)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 8.98/9.18  thf('63', plain,
% 8.98/9.18      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['49', '62'])).
% 8.98/9.18  thf('64', plain,
% 8.98/9.18      (![X32 : $i, X33 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.98/9.18  thf('65', plain,
% 8.98/9.18      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['57'])).
% 8.98/9.18  thf(dt_k6_partfun1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( m1_subset_1 @
% 8.98/9.18         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 8.98/9.18       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 8.98/9.18  thf('66', plain,
% 8.98/9.18      (![X41 : $i]:
% 8.98/9.18         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 8.98/9.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 8.98/9.18  thf(redefinition_k6_partfun1, axiom,
% 8.98/9.18    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.98/9.18  thf('67', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.98/9.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.18  thf('68', plain,
% 8.98/9.18      (![X41 : $i]:
% 8.98/9.18         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 8.98/9.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 8.98/9.18      inference('demod', [status(thm)], ['66', '67'])).
% 8.98/9.18  thf('69', plain,
% 8.98/9.18      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['65', '68'])).
% 8.98/9.18  thf('70', plain,
% 8.98/9.18      (![X9 : $i, X10 : $i]:
% 8.98/9.18         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_subset])).
% 8.98/9.18  thf('71', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 8.98/9.18      inference('sup-', [status(thm)], ['69', '70'])).
% 8.98/9.18  thf(t3_xboole_1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.98/9.18  thf('72', plain,
% 8.98/9.18      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 8.98/9.18  thf('73', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['71', '72'])).
% 8.98/9.18  thf(t71_relat_1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.98/9.18       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.98/9.18  thf('74', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 8.98/9.18      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.98/9.18  thf('75', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['73', '74'])).
% 8.98/9.18  thf('76', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         (((k2_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 8.98/9.18      inference('sup+', [status(thm)], ['64', '75'])).
% 8.98/9.18  thf('77', plain,
% 8.98/9.18      (![X6 : $i, X7 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.98/9.18  thf('78', plain,
% 8.98/9.18      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['77'])).
% 8.98/9.18  thf('79', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ (k2_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 8.98/9.18          | (zip_tseitin_0 @ X0 @ X2))),
% 8.98/9.18      inference('sup+', [status(thm)], ['76', '78'])).
% 8.98/9.18  thf('80', plain,
% 8.98/9.18      (![X21 : $i]:
% 8.98/9.18         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 8.98/9.18          | ~ (v1_funct_1 @ X21)
% 8.98/9.18          | ~ (v1_relat_1 @ X21))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.98/9.18  thf('81', plain,
% 8.98/9.18      (![X21 : $i]:
% 8.98/9.18         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 8.98/9.18          | ~ (v1_funct_1 @ X21)
% 8.98/9.18          | ~ (v1_relat_1 @ X21))),
% 8.98/9.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.98/9.18  thf('82', plain,
% 8.98/9.18      (![X22 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X22)
% 8.98/9.18          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 8.98/9.18          | ~ (v1_funct_1 @ X22)
% 8.98/9.18          | ~ (v1_relat_1 @ X22))),
% 8.98/9.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.98/9.18  thf('83', plain,
% 8.98/9.18      (![X43 : $i]:
% 8.98/9.18         ((m1_subset_1 @ X43 @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 8.98/9.18          | ~ (v1_funct_1 @ X43)
% 8.98/9.18          | ~ (v1_relat_1 @ X43))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_funct_2])).
% 8.98/9.18  thf('84', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 8.98/9.18      inference('sup+', [status(thm)], ['82', '83'])).
% 8.98/9.18  thf('85', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18             (k1_zfmisc_1 @ 
% 8.98/9.18              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 8.98/9.18               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['81', '84'])).
% 8.98/9.18  thf('86', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['85'])).
% 8.98/9.18  thf('87', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18             (k1_zfmisc_1 @ 
% 8.98/9.18              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 8.98/9.18               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['80', '86'])).
% 8.98/9.18  thf('88', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['87'])).
% 8.98/9.18  thf('89', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.98/9.18          | (zip_tseitin_0 @ X0 @ X1)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['79', '88'])).
% 8.98/9.18  thf('90', plain,
% 8.98/9.18      (![X9 : $i, X10 : $i]:
% 8.98/9.18         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_subset])).
% 8.98/9.18  thf('91', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | (zip_tseitin_0 @ X0 @ X1)
% 8.98/9.18          | (r1_tarski @ (k2_funct_1 @ X0) @ k1_xboole_0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['89', '90'])).
% 8.98/9.18  thf('92', plain,
% 8.98/9.18      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 8.98/9.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 8.98/9.18  thf('93', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X0 @ X1)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['91', '92'])).
% 8.98/9.18  thf('94', plain,
% 8.98/9.18      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['49', '62'])).
% 8.98/9.18  thf('95', plain,
% 8.98/9.18      ((![X0 : $i]:
% 8.98/9.18          (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 8.98/9.18           | ~ (v2_funct_1 @ k1_xboole_0)
% 8.98/9.18           | ~ (v1_funct_1 @ k1_xboole_0)
% 8.98/9.18           | ~ (v1_relat_1 @ k1_xboole_0)
% 8.98/9.18           | (zip_tseitin_0 @ k1_xboole_0 @ X0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['93', '94'])).
% 8.98/9.18  thf(t4_subset_1, axiom,
% 8.98/9.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 8.98/9.18  thf('96', plain,
% 8.98/9.18      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 8.98/9.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.98/9.18  thf('97', plain,
% 8.98/9.18      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.98/9.18         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 8.98/9.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.98/9.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.98/9.18  thf('98', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['96', '97'])).
% 8.98/9.18  thf('99', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['71', '72'])).
% 8.98/9.18  thf('100', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 8.98/9.18      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.98/9.18  thf('101', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['99', '100'])).
% 8.98/9.18  thf('102', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('demod', [status(thm)], ['98', '101'])).
% 8.98/9.18  thf('103', plain,
% 8.98/9.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.98/9.18         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 8.98/9.18          | (v1_funct_2 @ X36 @ X34 @ X35)
% 8.98/9.18          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.98/9.18  thf('104', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         (((X1) != (k1_xboole_0))
% 8.98/9.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 8.98/9.18          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['102', '103'])).
% 8.98/9.18  thf('105', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.98/9.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['104'])).
% 8.98/9.18  thf('106', plain,
% 8.98/9.18      (![X32 : $i, X33 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.98/9.18  thf('107', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 8.98/9.18      inference('simplify', [status(thm)], ['106'])).
% 8.98/9.18  thf('108', plain,
% 8.98/9.18      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 8.98/9.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.98/9.18  thf('109', plain,
% 8.98/9.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.98/9.18         (~ (zip_tseitin_0 @ X37 @ X38)
% 8.98/9.18          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 8.98/9.18          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.98/9.18  thf('110', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 8.98/9.18      inference('sup-', [status(thm)], ['108', '109'])).
% 8.98/9.18  thf('111', plain,
% 8.98/9.18      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 8.98/9.18      inference('sup-', [status(thm)], ['107', '110'])).
% 8.98/9.18  thf('112', plain,
% 8.98/9.18      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.98/9.18      inference('simplify_reflect+', [status(thm)], ['105', '111'])).
% 8.98/9.18  thf('113', plain,
% 8.98/9.18      ((((k1_xboole_0) = (sk_C)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 8.98/9.18  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('115', plain,
% 8.98/9.18      (((v2_funct_1 @ k1_xboole_0))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup+', [status(thm)], ['113', '114'])).
% 8.98/9.18  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('117', plain,
% 8.98/9.18      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 8.98/9.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.98/9.18  thf(cc3_funct_1, axiom,
% 8.98/9.18    (![A:$i]:
% 8.98/9.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.98/9.18       ( ![B:$i]:
% 8.98/9.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 8.98/9.18  thf('118', plain,
% 8.98/9.18      (![X19 : $i, X20 : $i]:
% 8.98/9.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 8.98/9.18          | (v1_funct_1 @ X19)
% 8.98/9.18          | ~ (v1_funct_1 @ X20)
% 8.98/9.18          | ~ (v1_relat_1 @ X20))),
% 8.98/9.18      inference('cnf', [status(esa)], [cc3_funct_1])).
% 8.98/9.18  thf('119', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | (v1_funct_1 @ k1_xboole_0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['117', '118'])).
% 8.98/9.18  thf('120', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C))),
% 8.98/9.18      inference('sup-', [status(thm)], ['116', '119'])).
% 8.98/9.18  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.18      inference('sup-', [status(thm)], ['2', '3'])).
% 8.98/9.18  thf('122', plain, ((v1_funct_1 @ k1_xboole_0)),
% 8.98/9.18      inference('demod', [status(thm)], ['120', '121'])).
% 8.98/9.18  thf('123', plain,
% 8.98/9.18      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['77'])).
% 8.98/9.18  thf(fc6_relat_1, axiom,
% 8.98/9.18    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.98/9.18  thf('124', plain,
% 8.98/9.18      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 8.98/9.18      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.98/9.18  thf('125', plain, ((v1_relat_1 @ k1_xboole_0)),
% 8.98/9.18      inference('sup+', [status(thm)], ['123', '124'])).
% 8.98/9.18  thf('126', plain,
% 8.98/9.18      ((![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['95', '112', '115', '122', '125'])).
% 8.98/9.18  thf('127', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 8.98/9.18      inference('sup-', [status(thm)], ['108', '109'])).
% 8.98/9.18  thf('128', plain,
% 8.98/9.18      ((![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['126', '127'])).
% 8.98/9.18  thf('129', plain,
% 8.98/9.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.98/9.18         (((X37) != (k1_xboole_0))
% 8.98/9.18          | ((X38) = (k1_xboole_0))
% 8.98/9.18          | (v1_funct_2 @ X39 @ X38 @ X37)
% 8.98/9.18          | ((X39) != (k1_xboole_0))
% 8.98/9.18          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.98/9.18  thf('130', plain,
% 8.98/9.18      (![X38 : $i]:
% 8.98/9.18         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 8.98/9.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ k1_xboole_0)))
% 8.98/9.18          | (v1_funct_2 @ k1_xboole_0 @ X38 @ k1_xboole_0)
% 8.98/9.18          | ((X38) = (k1_xboole_0)))),
% 8.98/9.18      inference('simplify', [status(thm)], ['129'])).
% 8.98/9.18  thf('131', plain,
% 8.98/9.18      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['57'])).
% 8.98/9.18  thf('132', plain,
% 8.98/9.18      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 8.98/9.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.98/9.18  thf('133', plain,
% 8.98/9.18      (![X38 : $i]:
% 8.98/9.18         ((v1_funct_2 @ k1_xboole_0 @ X38 @ k1_xboole_0)
% 8.98/9.18          | ((X38) = (k1_xboole_0)))),
% 8.98/9.18      inference('demod', [status(thm)], ['130', '131', '132'])).
% 8.98/9.18  thf('134', plain,
% 8.98/9.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.98/9.18         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 8.98/9.18          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 8.98/9.18          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.98/9.18  thf('135', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((X0) = (k1_xboole_0))
% 8.98/9.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.98/9.18          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['133', '134'])).
% 8.98/9.18  thf('136', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.18      inference('demod', [status(thm)], ['98', '101'])).
% 8.98/9.18  thf('137', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((X0) = (k1_xboole_0))
% 8.98/9.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.98/9.18          | ((X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('demod', [status(thm)], ['135', '136'])).
% 8.98/9.18  thf('138', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.98/9.18          | ((X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('simplify', [status(thm)], ['137'])).
% 8.98/9.18  thf('139', plain,
% 8.98/9.18      ((![X0 : $i]: ((X0) = (k1_xboole_0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['128', '138'])).
% 8.98/9.18  thf('140', plain,
% 8.98/9.18      ((![X0 : $i]: ((X0) = (k1_xboole_0)))
% 8.98/9.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['128', '138'])).
% 8.98/9.18  thf('141', plain,
% 8.98/9.18      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.98/9.18      inference('simplify_reflect+', [status(thm)], ['105', '111'])).
% 8.98/9.18  thf('142', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 8.98/9.18      inference('demod', [status(thm)], ['63', '139', '140', '141'])).
% 8.98/9.18  thf('143', plain,
% 8.98/9.18      (~
% 8.98/9.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 8.98/9.18       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 8.98/9.18       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf('144', plain,
% 8.98/9.18      (~
% 8.98/9.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 8.98/9.18      inference('sat_resolution*', [status(thm)], ['10', '142', '143'])).
% 8.98/9.18  thf('145', plain,
% 8.98/9.18      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.18      inference('simpl_trail', [status(thm)], ['1', '144'])).
% 8.98/9.18  thf('146', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.98/9.18      inference('sup+', [status(thm)], ['40', '41'])).
% 8.98/9.18  thf('147', plain,
% 8.98/9.18      (![X22 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X22)
% 8.98/9.18          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 8.98/9.18          | ~ (v1_funct_1 @ X22)
% 8.98/9.18          | ~ (v1_relat_1 @ X22))),
% 8.98/9.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.98/9.18  thf('148', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['87'])).
% 8.98/9.18  thf('149', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v2_funct_1 @ X0))),
% 8.98/9.18      inference('sup+', [status(thm)], ['147', '148'])).
% 8.98/9.18  thf('150', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0)
% 8.98/9.18          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18             (k1_zfmisc_1 @ 
% 8.98/9.18              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 8.98/9.18      inference('simplify', [status(thm)], ['149'])).
% 8.98/9.18  thf('151', plain,
% 8.98/9.18      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 8.98/9.18        | ~ (v1_relat_1 @ sk_C)
% 8.98/9.18        | ~ (v1_funct_1 @ sk_C)
% 8.98/9.18        | ~ (v2_funct_1 @ sk_C))),
% 8.98/9.18      inference('sup+', [status(thm)], ['146', '150'])).
% 8.98/9.18  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.18      inference('sup-', [status(thm)], ['2', '3'])).
% 8.98/9.18  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('155', plain,
% 8.98/9.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 8.98/9.18      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 8.98/9.18  thf('156', plain,
% 8.98/9.18      (![X32 : $i, X33 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.98/9.18  thf('157', plain,
% 8.98/9.18      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['77'])).
% 8.98/9.18  thf('158', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 8.98/9.18      inference('sup+', [status(thm)], ['156', '157'])).
% 8.98/9.18  thf('159', plain,
% 8.98/9.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 8.98/9.18      inference('sup-', [status(thm)], ['13', '14'])).
% 8.98/9.18  thf('160', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 8.98/9.18          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 8.98/9.18      inference('sup-', [status(thm)], ['158', '159'])).
% 8.98/9.18  thf('161', plain,
% 8.98/9.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('demod', [status(thm)], ['19', '22'])).
% 8.98/9.18  thf('162', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 8.98/9.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['160', '161'])).
% 8.98/9.18  thf('163', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 8.98/9.18           (k1_zfmisc_1 @ 
% 8.98/9.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 8.98/9.18          | ~ (v2_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_funct_1 @ X0)
% 8.98/9.18          | ~ (v1_relat_1 @ X0))),
% 8.98/9.18      inference('simplify', [status(thm)], ['87'])).
% 8.98/9.18  thf('164', plain,
% 8.98/9.18      (![X32 : $i, X33 : $i]:
% 8.98/9.18         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.98/9.18  thf('165', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 8.98/9.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['160', '161'])).
% 8.98/9.18  thf('166', plain,
% 8.98/9.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('split', [status(esa)], ['0'])).
% 8.98/9.18  thf('167', plain,
% 8.98/9.18      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.98/9.18         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['165', '166'])).
% 8.98/9.18  thf('168', plain,
% 8.98/9.18      ((![X0 : $i, X1 : $i]:
% 8.98/9.18          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 8.98/9.18           | (zip_tseitin_0 @ X0 @ X1)
% 8.98/9.18           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['164', '167'])).
% 8.98/9.18  thf('169', plain,
% 8.98/9.18      ((![X0 : $i]:
% 8.98/9.18          (~ (v1_relat_1 @ sk_C)
% 8.98/9.18           | ~ (v1_funct_1 @ sk_C)
% 8.98/9.18           | ~ (v2_funct_1 @ sk_C)
% 8.98/9.18           | ((sk_A) = (k1_relat_1 @ sk_C))
% 8.98/9.18           | (zip_tseitin_0 @ 
% 8.98/9.18              (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ 
% 8.98/9.18               (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 8.98/9.18              X0)))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('sup-', [status(thm)], ['163', '168'])).
% 8.98/9.18  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.18      inference('sup-', [status(thm)], ['2', '3'])).
% 8.98/9.18  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 8.98/9.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.18  thf('173', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.98/9.18      inference('sup+', [status(thm)], ['40', '41'])).
% 8.98/9.18  thf('174', plain,
% 8.98/9.18      ((![X0 : $i]:
% 8.98/9.18          (((sk_A) = (k1_relat_1 @ sk_C))
% 8.98/9.18           | (zip_tseitin_0 @ 
% 8.98/9.18              (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ X0)))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 8.98/9.18  thf('175', plain,
% 8.98/9.18      ((![X0 : $i]:
% 8.98/9.18          ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 8.98/9.18           | ((sk_A) = (k1_relat_1 @ sk_C))
% 8.98/9.18           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('sup+', [status(thm)], ['162', '174'])).
% 8.98/9.18  thf('176', plain,
% 8.98/9.18      ((![X0 : $i]:
% 8.98/9.18          (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ k1_xboole_0 @ X0)))
% 8.98/9.18         <= (~
% 8.98/9.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 8.98/9.18      inference('simplify', [status(thm)], ['175'])).
% 8.98/9.18  thf('177', plain,
% 8.98/9.18      (~
% 8.98/9.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 8.98/9.18      inference('sat_resolution*', [status(thm)], ['10', '142', '143'])).
% 8.98/9.18  thf('178', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ k1_xboole_0 @ X0))),
% 8.98/9.18      inference('simpl_trail', [status(thm)], ['176', '177'])).
% 8.98/9.18  thf('179', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 8.98/9.18      inference('sup-', [status(thm)], ['108', '109'])).
% 8.98/9.18  thf('180', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (((sk_A) = (k1_relat_1 @ sk_C))
% 8.98/9.18          | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 8.98/9.18      inference('sup-', [status(thm)], ['178', '179'])).
% 8.98/9.18  thf('181', plain,
% 8.98/9.18      (![X0 : $i]:
% 8.98/9.18         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 8.98/9.18          | ((X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('simplify', [status(thm)], ['137'])).
% 8.98/9.18  thf('182', plain,
% 8.98/9.18      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['180', '181'])).
% 8.98/9.18  thf('183', plain,
% 8.98/9.18      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X0) = (k1_xboole_0)))),
% 8.98/9.18      inference('sup-', [status(thm)], ['180', '181'])).
% 8.98/9.18  thf('184', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]:
% 8.98/9.18         (((X1) = (X0))
% 8.98/9.18          | ((sk_A) = (k1_relat_1 @ sk_C))
% 8.98/9.18          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.98/9.18      inference('sup+', [status(thm)], ['182', '183'])).
% 8.98/9.18  thf('185', plain,
% 8.98/9.18      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | ((X1) = (X0)))),
% 8.98/9.18      inference('simplify', [status(thm)], ['184'])).
% 8.98/9.18  thf('186', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 8.98/9.18      inference('condensation', [status(thm)], ['185'])).
% 8.98/9.18  thf('187', plain,
% 8.98/9.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 8.98/9.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.18      inference('demod', [status(thm)], ['155', '186'])).
% 8.98/9.18  thf('188', plain, ($false), inference('demod', [status(thm)], ['145', '187'])).
% 8.98/9.18  
% 8.98/9.18  % SZS output end Refutation
% 8.98/9.18  
% 9.02/9.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
