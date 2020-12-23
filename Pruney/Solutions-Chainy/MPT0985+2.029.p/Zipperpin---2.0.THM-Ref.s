%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWtnJPrZsg

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:30 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  237 (5160 expanded)
%              Number of leaves         :   40 (1498 expanded)
%              Depth                    :   25
%              Number of atoms          : 2057 (84256 expanded)
%              Number of equality atoms :  125 (3790 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
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
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
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
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
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
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','48'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X10: $i] :
      ( ( ( k2_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('53',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('55',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('62',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','70'])).

thf('72',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('74',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','57','74'])).

thf('76',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('77',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('78',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('83',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','81','84'])).

thf('86',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('87',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ k1_xboole_0 )
      = sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('93',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_relset_1 @ X4 @ X3 @ X0 )
        = ( k2_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relset_1 @ X4 @ X3 @ X0 )
        = ( k2_relset_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relset_1 @ X3 @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('107',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','105','106'])).

thf('108',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('109',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('110',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','107','110'])).

thf('112',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('114',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('118',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ X2 )
      | ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','57','74'])).

thf('129',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('132',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('134',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('135',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['131','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('143',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['130','145'])).

thf('147',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('148',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('149',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('150',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('151',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','105','106'])).

thf('152',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['75','129','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','153','154'])).

thf('156',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('158',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('159',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('162',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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

thf('168',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['158','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['157','169'])).

thf('171',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('176',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('177',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('181',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('182',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182','183'])).

thf('185',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('186',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('188',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','153','154'])).

thf('190',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('192',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','190','191','192','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['156','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWtnJPrZsg
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.30/1.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.51  % Solved by: fo/fo7.sh
% 1.30/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.51  % done 1919 iterations in 1.061s
% 1.30/1.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.51  % SZS output start Refutation
% 1.30/1.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.30/1.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.30/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.30/1.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.30/1.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.30/1.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.30/1.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.30/1.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.30/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.30/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.30/1.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.30/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.30/1.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.30/1.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.30/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.51  thf(t31_funct_2, conjecture,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.30/1.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.30/1.51         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.30/1.51           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.30/1.51           ( m1_subset_1 @
% 1.30/1.51             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.51    (~( ![A:$i,B:$i,C:$i]:
% 1.30/1.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.30/1.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.30/1.51            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.30/1.51              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.30/1.51              ( m1_subset_1 @
% 1.30/1.51                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.30/1.51    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.30/1.51  thf('0', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.30/1.51        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.30/1.51        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('1', plain,
% 1.30/1.51      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.30/1.51         <= (~
% 1.30/1.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.51      inference('split', [status(esa)], ['0'])).
% 1.30/1.51  thf('2', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(cc1_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( v1_relat_1 @ C ) ))).
% 1.30/1.51  thf('3', plain,
% 1.30/1.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.30/1.51         ((v1_relat_1 @ X14)
% 1.30/1.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.30/1.51  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.51      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.51  thf(dt_k2_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.30/1.51         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.30/1.51  thf('5', plain,
% 1.30/1.51      (![X12 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 1.30/1.51          | ~ (v1_funct_1 @ X12)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('6', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.30/1.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.30/1.51      inference('split', [status(esa)], ['0'])).
% 1.30/1.51  thf('7', plain,
% 1.30/1.51      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 1.30/1.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.51  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('9', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.30/1.51      inference('demod', [status(thm)], ['7', '8'])).
% 1.30/1.51  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['4', '9'])).
% 1.30/1.51  thf('11', plain,
% 1.30/1.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('split', [status(esa)], ['0'])).
% 1.30/1.51  thf(d1_funct_2, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.30/1.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.30/1.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.30/1.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.30/1.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.30/1.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_1, axiom,
% 1.30/1.51    (![B:$i,A:$i]:
% 1.30/1.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.30/1.51       ( zip_tseitin_0 @ B @ A ) ))).
% 1.30/1.51  thf('12', plain,
% 1.30/1.51      (![X23 : $i, X24 : $i]:
% 1.30/1.51         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.30/1.51  thf('13', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.30/1.51  thf(zf_stmt_3, axiom,
% 1.30/1.51    (![C:$i,B:$i,A:$i]:
% 1.30/1.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.30/1.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.30/1.51  thf(zf_stmt_5, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.30/1.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.30/1.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.30/1.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.30/1.51  thf('14', plain,
% 1.30/1.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.51         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.30/1.51          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.30/1.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.30/1.51  thf('15', plain,
% 1.30/1.51      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.30/1.51        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf('16', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['12', '15'])).
% 1.30/1.51  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('18', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.30/1.51         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.30/1.51          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.30/1.51          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.30/1.51  thf('19', plain,
% 1.30/1.51      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.30/1.51        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['17', '18'])).
% 1.30/1.51  thf('20', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(redefinition_k1_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.30/1.51  thf('21', plain,
% 1.30/1.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.30/1.51         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.30/1.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.30/1.51  thf('22', plain,
% 1.30/1.51      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['20', '21'])).
% 1.30/1.51  thf('23', plain,
% 1.30/1.51      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.30/1.51        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.30/1.51      inference('demod', [status(thm)], ['19', '22'])).
% 1.30/1.51  thf('24', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '23'])).
% 1.30/1.51  thf(t55_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v2_funct_1 @ A ) =>
% 1.30/1.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.30/1.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.30/1.51  thf('25', plain,
% 1.30/1.51      (![X13 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X13)
% 1.30/1.51          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.51          | ~ (v1_funct_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X13))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('26', plain,
% 1.30/1.51      (![X12 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 1.30/1.51          | ~ (v1_funct_1 @ X12)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('27', plain,
% 1.30/1.51      (![X12 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 1.30/1.51          | ~ (v1_funct_1 @ X12)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('28', plain,
% 1.30/1.51      (![X13 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X13)
% 1.30/1.51          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.51          | ~ (v1_funct_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X13))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf(t3_funct_2, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v1_funct_1 @ A ) & 
% 1.30/1.51         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.30/1.51         ( m1_subset_1 @
% 1.30/1.51           A @ 
% 1.30/1.51           ( k1_zfmisc_1 @
% 1.30/1.51             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.30/1.51  thf('29', plain,
% 1.30/1.51      (![X31 : $i]:
% 1.30/1.51         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.30/1.51          | ~ (v1_funct_1 @ X31)
% 1.30/1.51          | ~ (v1_relat_1 @ X31))),
% 1.30/1.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.30/1.51  thf('30', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.30/1.51           (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['28', '29'])).
% 1.30/1.51  thf('31', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.30/1.51             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['27', '30'])).
% 1.30/1.51  thf('32', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.30/1.51           (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['31'])).
% 1.30/1.51  thf('33', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.30/1.51             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['26', '32'])).
% 1.30/1.51  thf('34', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.30/1.51           (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['33'])).
% 1.30/1.51  thf('35', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.51           (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['25', '34'])).
% 1.30/1.51  thf('36', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.51             (k1_relat_1 @ X0)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['35'])).
% 1.30/1.51  thf('37', plain,
% 1.30/1.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 1.30/1.51        | ((sk_B_1) = (k1_xboole_0))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C_1)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C_1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['24', '36'])).
% 1.30/1.51  thf('38', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(redefinition_k2_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.30/1.51  thf('39', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.30/1.51         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.30/1.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.30/1.51  thf('40', plain,
% 1.30/1.51      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['38', '39'])).
% 1.30/1.51  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('42', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.51  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.51      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.51  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('45', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('46', plain,
% 1.30/1.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.30/1.51        | ((sk_B_1) = (k1_xboole_0)))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 1.30/1.51  thf('47', plain,
% 1.30/1.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('split', [status(esa)], ['0'])).
% 1.30/1.51  thf('48', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.51  thf('49', plain,
% 1.30/1.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['11', '48'])).
% 1.30/1.51  thf('50', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.51  thf('51', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.51  thf(t64_relat_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ A ) =>
% 1.30/1.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.30/1.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.30/1.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.30/1.51  thf('52', plain,
% 1.30/1.51      (![X10 : $i]:
% 1.30/1.51         (((k2_relat_1 @ X10) != (k1_xboole_0))
% 1.30/1.51          | ((X10) = (k1_xboole_0))
% 1.30/1.51          | ~ (v1_relat_1 @ X10))),
% 1.30/1.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.30/1.51  thf('53', plain,
% 1.30/1.51      ((((sk_B_1) != (k1_xboole_0))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.51        | ((sk_C_1) = (k1_xboole_0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['51', '52'])).
% 1.30/1.51  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.51      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.51  thf('55', plain,
% 1.30/1.51      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.30/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.30/1.51  thf('56', plain,
% 1.30/1.51      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0))))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['50', '55'])).
% 1.30/1.51  thf('57', plain,
% 1.30/1.51      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('58', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.51  thf('59', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.51  thf('60', plain,
% 1.30/1.51      (![X12 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 1.30/1.51          | ~ (v1_funct_1 @ X12)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('61', plain,
% 1.30/1.51      (![X13 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X13)
% 1.30/1.51          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.51          | ~ (v1_funct_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X13))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('62', plain,
% 1.30/1.51      (![X10 : $i]:
% 1.30/1.51         (((k1_relat_1 @ X10) != (k1_xboole_0))
% 1.30/1.51          | ((X10) = (k1_xboole_0))
% 1.30/1.51          | ~ (v1_relat_1 @ X10))),
% 1.30/1.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.30/1.51  thf('63', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['61', '62'])).
% 1.30/1.51  thf('64', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['60', '63'])).
% 1.30/1.51  thf('65', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['64'])).
% 1.30/1.51  thf('66', plain,
% 1.30/1.51      ((((sk_B_1) != (k1_xboole_0))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C_1)
% 1.30/1.51        | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C_1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['59', '65'])).
% 1.30/1.51  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.51      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.51  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('69', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('70', plain,
% 1.30/1.51      ((((sk_B_1) != (k1_xboole_0)) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.30/1.51      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 1.30/1.51  thf('71', plain,
% 1.30/1.51      (((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.51         | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['58', '70'])).
% 1.30/1.51  thf('72', plain,
% 1.30/1.51      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['71'])).
% 1.30/1.51  thf('73', plain,
% 1.30/1.51      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('74', plain,
% 1.30/1.51      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['72', '73'])).
% 1.30/1.51  thf('75', plain,
% 1.30/1.51      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['49', '57', '74'])).
% 1.30/1.51  thf('76', plain,
% 1.30/1.51      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['72', '73'])).
% 1.30/1.51  thf('77', plain,
% 1.30/1.51      (![X13 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X13)
% 1.30/1.51          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.51          | ~ (v1_funct_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X13))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('78', plain,
% 1.30/1.51      (((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 1.30/1.51         | ~ (v1_relat_1 @ k1_xboole_0)
% 1.30/1.51         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.30/1.51         | ~ (v2_funct_1 @ k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['76', '77'])).
% 1.30/1.51  thf('79', plain,
% 1.30/1.51      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('81', plain,
% 1.30/1.51      (((v1_funct_1 @ k1_xboole_0))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['79', '80'])).
% 1.30/1.51  thf('82', plain,
% 1.30/1.51      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('83', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('84', plain,
% 1.30/1.51      (((v2_funct_1 @ k1_xboole_0))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['82', '83'])).
% 1.30/1.51  thf('85', plain,
% 1.30/1.51      (((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 1.30/1.51         | ~ (v1_relat_1 @ k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['78', '81', '84'])).
% 1.30/1.51  thf('86', plain,
% 1.30/1.51      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('87', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('88', plain,
% 1.30/1.51      ((((k2_relset_1 @ sk_A @ sk_B_1 @ k1_xboole_0) = (sk_B_1)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['86', '87'])).
% 1.30/1.51  thf('89', plain,
% 1.30/1.51      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.51  thf(d3_tarski, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.51  thf('90', plain,
% 1.30/1.51      (![X4 : $i, X6 : $i]:
% 1.30/1.51         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.51      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.51  thf(d1_xboole_0, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.30/1.51  thf('91', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.51  thf('92', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['90', '91'])).
% 1.30/1.51  thf(t3_subset, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.30/1.51  thf('93', plain,
% 1.30/1.51      (![X7 : $i, X9 : $i]:
% 1.30/1.51         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.30/1.51      inference('cnf', [status(esa)], [t3_subset])).
% 1.30/1.51  thf('94', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['92', '93'])).
% 1.30/1.51  thf('95', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.30/1.51         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.30/1.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.30/1.51  thf('96', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (~ (v1_xboole_0 @ X2)
% 1.30/1.51          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['94', '95'])).
% 1.30/1.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.30/1.51  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.30/1.51  thf('98', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (~ (v1_xboole_0 @ X2)
% 1.30/1.51          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['94', '95'])).
% 1.30/1.51  thf('99', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X2)
% 1.30/1.52          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['94', '95'])).
% 1.30/1.52  thf('100', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.30/1.52         (((k2_relset_1 @ X4 @ X3 @ X0) = (k2_relset_1 @ X2 @ X1 @ X0))
% 1.30/1.52          | ~ (v1_xboole_0 @ X0)
% 1.30/1.52          | ~ (v1_xboole_0 @ X0))),
% 1.30/1.52      inference('sup+', [status(thm)], ['98', '99'])).
% 1.30/1.52  thf('101', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X0)
% 1.30/1.52          | ((k2_relset_1 @ X4 @ X3 @ X0) = (k2_relset_1 @ X2 @ X1 @ X0)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['100'])).
% 1.30/1.52  thf('102', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.52         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0)
% 1.30/1.52           = (k2_relset_1 @ X3 @ X2 @ k1_xboole_0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['97', '101'])).
% 1.30/1.52  thf('103', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         (((k2_relat_1 @ k1_xboole_0) = (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 1.30/1.52          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.30/1.52      inference('sup+', [status(thm)], ['96', '102'])).
% 1.30/1.52  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.30/1.52  thf('105', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((k2_relat_1 @ k1_xboole_0) = (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.30/1.52      inference('demod', [status(thm)], ['103', '104'])).
% 1.30/1.52  thf('106', plain,
% 1.30/1.52      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.52  thf('107', plain,
% 1.30/1.52      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['88', '89', '105', '106'])).
% 1.30/1.52  thf('108', plain,
% 1.30/1.52      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.52  thf('109', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.52  thf('110', plain,
% 1.30/1.52      (((v1_relat_1 @ k1_xboole_0))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['108', '109'])).
% 1.30/1.52  thf('111', plain,
% 1.30/1.52      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['85', '107', '110'])).
% 1.30/1.52  thf('112', plain,
% 1.30/1.52      (![X23 : $i, X24 : $i]:
% 1.30/1.52         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.30/1.52  thf('113', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['92', '93'])).
% 1.30/1.52  thf('114', plain,
% 1.30/1.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.52         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.30/1.52          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.30/1.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.30/1.52  thf('115', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X2)
% 1.30/1.52          | (zip_tseitin_1 @ X2 @ X0 @ X1)
% 1.30/1.52          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['113', '114'])).
% 1.30/1.52  thf('116', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (((X1) = (k1_xboole_0))
% 1.30/1.52          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 1.30/1.52          | ~ (v1_xboole_0 @ X2))),
% 1.30/1.52      inference('sup-', [status(thm)], ['112', '115'])).
% 1.30/1.52  thf('117', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['92', '93'])).
% 1.30/1.52  thf('118', plain,
% 1.30/1.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.30/1.52         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.30/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.30/1.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.30/1.52  thf('119', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X2)
% 1.30/1.52          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['117', '118'])).
% 1.30/1.52  thf('120', plain,
% 1.30/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.30/1.52         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 1.30/1.52          | (v1_funct_2 @ X27 @ X25 @ X26)
% 1.30/1.52          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.30/1.52  thf('121', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (((X2) != (k1_relat_1 @ X0))
% 1.30/1.52          | ~ (v1_xboole_0 @ X0)
% 1.30/1.52          | ~ (zip_tseitin_1 @ X0 @ X1 @ X2)
% 1.30/1.52          | (v1_funct_2 @ X0 @ X2 @ X1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['119', '120'])).
% 1.30/1.52  thf('122', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 1.30/1.52          | ~ (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 1.30/1.52          | ~ (v1_xboole_0 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['121'])).
% 1.30/1.52  thf('123', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X0)
% 1.30/1.52          | ((X1) = (k1_xboole_0))
% 1.30/1.52          | ~ (v1_xboole_0 @ X0)
% 1.30/1.52          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['116', '122'])).
% 1.30/1.52  thf('124', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 1.30/1.52          | ((X1) = (k1_xboole_0))
% 1.30/1.52          | ~ (v1_xboole_0 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['123'])).
% 1.30/1.52  thf('125', plain,
% 1.30/1.52      ((![X0 : $i]:
% 1.30/1.52          ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.30/1.52           | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.30/1.52           | ((X0) = (k1_xboole_0))))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['111', '124'])).
% 1.30/1.52  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.30/1.52  thf('127', plain,
% 1.30/1.52      ((![X0 : $i]:
% 1.30/1.52          ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.30/1.52           | ((X0) = (k1_xboole_0))))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['125', '126'])).
% 1.30/1.52  thf('128', plain,
% 1.30/1.52      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['49', '57', '74'])).
% 1.30/1.52  thf('129', plain,
% 1.30/1.52      ((((sk_A) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['127', '128'])).
% 1.30/1.52  thf('130', plain,
% 1.30/1.52      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.52  thf('131', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.52      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.52  thf('132', plain,
% 1.30/1.52      (![X12 : $i]:
% 1.30/1.52         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 1.30/1.52          | ~ (v1_funct_1 @ X12)
% 1.30/1.52          | ~ (v1_relat_1 @ X12))),
% 1.30/1.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.52  thf('133', plain,
% 1.30/1.52      (![X12 : $i]:
% 1.30/1.52         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 1.30/1.52          | ~ (v1_funct_1 @ X12)
% 1.30/1.52          | ~ (v1_relat_1 @ X12))),
% 1.30/1.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.52  thf('134', plain,
% 1.30/1.52      (![X13 : $i]:
% 1.30/1.52         (~ (v2_funct_1 @ X13)
% 1.30/1.52          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.52          | ~ (v1_funct_1 @ X13)
% 1.30/1.52          | ~ (v1_relat_1 @ X13))),
% 1.30/1.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.52  thf('135', plain,
% 1.30/1.52      (![X31 : $i]:
% 1.30/1.52         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.30/1.52          | ~ (v1_funct_1 @ X31)
% 1.30/1.52          | ~ (v1_relat_1 @ X31))),
% 1.30/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.30/1.52  thf('136', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.52           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['134', '135'])).
% 1.30/1.52  thf('137', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.52             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['133', '136'])).
% 1.30/1.52  thf('138', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.52           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['137'])).
% 1.30/1.52  thf('139', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.52             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['132', '138'])).
% 1.30/1.52  thf('140', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.30/1.52           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['139'])).
% 1.30/1.52  thf('141', plain,
% 1.30/1.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 1.30/1.52         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.30/1.52        | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.52        | ~ (v1_funct_1 @ sk_C_1)
% 1.30/1.52        | ~ (v2_funct_1 @ sk_C_1))),
% 1.30/1.52      inference('sup+', [status(thm)], ['131', '140'])).
% 1.30/1.52  thf('142', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.52  thf('143', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('144', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('145', plain,
% 1.30/1.52      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 1.30/1.52        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.30/1.52      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 1.30/1.52  thf('146', plain,
% 1.30/1.52      (((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ sk_B_1 @ 
% 1.30/1.52         (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['130', '145'])).
% 1.30/1.52  thf('147', plain,
% 1.30/1.52      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['72', '73'])).
% 1.30/1.52  thf('148', plain,
% 1.30/1.52      ((((sk_B_1) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.52  thf('149', plain,
% 1.30/1.52      ((((sk_C_1) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.52  thf('150', plain,
% 1.30/1.52      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['72', '73'])).
% 1.30/1.52  thf('151', plain,
% 1.30/1.52      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['88', '89', '105', '106'])).
% 1.30/1.52  thf('152', plain,
% 1.30/1.52      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.30/1.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)],
% 1.30/1.52                ['146', '147', '148', '149', '150', '151'])).
% 1.30/1.52  thf('153', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 1.30/1.52      inference('demod', [status(thm)], ['75', '129', '152'])).
% 1.30/1.52  thf('154', plain,
% 1.30/1.52      (~
% 1.30/1.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 1.30/1.52       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 1.30/1.52       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('155', plain,
% 1.30/1.52      (~
% 1.30/1.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.30/1.52      inference('sat_resolution*', [status(thm)], ['10', '153', '154'])).
% 1.30/1.52  thf('156', plain,
% 1.30/1.52      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('simpl_trail', [status(thm)], ['1', '155'])).
% 1.30/1.52  thf('157', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.52      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.52  thf('158', plain,
% 1.30/1.52      (![X13 : $i]:
% 1.30/1.52         (~ (v2_funct_1 @ X13)
% 1.30/1.52          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.52          | ~ (v1_funct_1 @ X13)
% 1.30/1.52          | ~ (v1_relat_1 @ X13))),
% 1.30/1.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.52  thf('159', plain,
% 1.30/1.52      (![X12 : $i]:
% 1.30/1.52         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 1.30/1.52          | ~ (v1_funct_1 @ X12)
% 1.30/1.52          | ~ (v1_relat_1 @ X12))),
% 1.30/1.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.52  thf('160', plain,
% 1.30/1.52      (![X12 : $i]:
% 1.30/1.52         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 1.30/1.52          | ~ (v1_funct_1 @ X12)
% 1.30/1.52          | ~ (v1_relat_1 @ X12))),
% 1.30/1.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.52  thf('161', plain,
% 1.30/1.52      (![X13 : $i]:
% 1.30/1.52         (~ (v2_funct_1 @ X13)
% 1.30/1.52          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 1.30/1.52          | ~ (v1_funct_1 @ X13)
% 1.30/1.52          | ~ (v1_relat_1 @ X13))),
% 1.30/1.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.52  thf('162', plain,
% 1.30/1.52      (![X31 : $i]:
% 1.30/1.52         ((m1_subset_1 @ X31 @ 
% 1.30/1.52           (k1_zfmisc_1 @ 
% 1.30/1.52            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.30/1.52          | ~ (v1_funct_1 @ X31)
% 1.30/1.52          | ~ (v1_relat_1 @ X31))),
% 1.30/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.30/1.52  thf('163', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52           (k1_zfmisc_1 @ 
% 1.30/1.52            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['161', '162'])).
% 1.30/1.52  thf('164', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52             (k1_zfmisc_1 @ 
% 1.30/1.52              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.30/1.52               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['160', '163'])).
% 1.30/1.52  thf('165', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52           (k1_zfmisc_1 @ 
% 1.30/1.52            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['164'])).
% 1.30/1.52  thf('166', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52             (k1_zfmisc_1 @ 
% 1.30/1.52              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.30/1.52               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['159', '165'])).
% 1.30/1.52  thf('167', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52           (k1_zfmisc_1 @ 
% 1.30/1.52            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['166'])).
% 1.30/1.52  thf('168', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v2_funct_1 @ X0))),
% 1.30/1.52      inference('sup+', [status(thm)], ['158', '167'])).
% 1.30/1.52  thf('169', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v2_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0)
% 1.30/1.52          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.30/1.52             (k1_zfmisc_1 @ 
% 1.30/1.52              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.30/1.52      inference('simplify', [status(thm)], ['168'])).
% 1.30/1.52  thf('170', plain,
% 1.30/1.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1))))
% 1.30/1.52        | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.52        | ~ (v1_funct_1 @ sk_C_1)
% 1.30/1.52        | ~ (v2_funct_1 @ sk_C_1))),
% 1.30/1.52      inference('sup+', [status(thm)], ['157', '169'])).
% 1.30/1.52  thf('171', plain,
% 1.30/1.52      (![X23 : $i, X24 : $i]:
% 1.30/1.52         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.30/1.52  thf('172', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.30/1.52          | ~ (v2_funct_1 @ X0)
% 1.30/1.52          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.30/1.52          | ~ (v1_funct_1 @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ X0))),
% 1.30/1.52      inference('simplify', [status(thm)], ['64'])).
% 1.30/1.52  thf('173', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         (((k2_relat_1 @ X1) != (X0))
% 1.30/1.52          | (zip_tseitin_0 @ X0 @ X2)
% 1.30/1.52          | ~ (v1_relat_1 @ X1)
% 1.30/1.52          | ~ (v1_funct_1 @ X1)
% 1.30/1.52          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.30/1.52          | ~ (v2_funct_1 @ X1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['171', '172'])).
% 1.30/1.52  thf('174', plain,
% 1.30/1.52      (![X1 : $i, X2 : $i]:
% 1.30/1.52         (~ (v2_funct_1 @ X1)
% 1.30/1.52          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.30/1.52          | ~ (v1_funct_1 @ X1)
% 1.30/1.52          | ~ (v1_relat_1 @ X1)
% 1.30/1.52          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 1.30/1.52      inference('simplify', [status(thm)], ['173'])).
% 1.30/1.52  thf('175', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['92', '93'])).
% 1.30/1.52  thf('176', plain,
% 1.30/1.52      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('177', plain,
% 1.30/1.52      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1)))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['175', '176'])).
% 1.30/1.52  thf('178', plain,
% 1.30/1.52      ((![X0 : $i]:
% 1.30/1.52          (~ (v1_xboole_0 @ k1_xboole_0)
% 1.30/1.52           | (zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ X0)
% 1.30/1.52           | ~ (v1_relat_1 @ sk_C_1)
% 1.30/1.52           | ~ (v1_funct_1 @ sk_C_1)
% 1.30/1.52           | ~ (v2_funct_1 @ sk_C_1)))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['174', '177'])).
% 1.30/1.52  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.30/1.52  thf('180', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.30/1.52      inference('sup+', [status(thm)], ['40', '41'])).
% 1.30/1.52  thf('181', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.52  thf('182', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('183', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('184', plain,
% 1.30/1.52      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('demod', [status(thm)],
% 1.30/1.52                ['178', '179', '180', '181', '182', '183'])).
% 1.30/1.52  thf('185', plain,
% 1.30/1.52      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.30/1.52        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.30/1.52      inference('sup-', [status(thm)], ['13', '14'])).
% 1.30/1.52  thf('186', plain,
% 1.30/1.52      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['184', '185'])).
% 1.30/1.52  thf('187', plain,
% 1.30/1.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.30/1.52        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.30/1.52      inference('demod', [status(thm)], ['19', '22'])).
% 1.30/1.52  thf('188', plain,
% 1.30/1.52      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 1.30/1.52         <= (~
% 1.30/1.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.30/1.52      inference('sup-', [status(thm)], ['186', '187'])).
% 1.30/1.52  thf('189', plain,
% 1.30/1.52      (~
% 1.30/1.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.30/1.52      inference('sat_resolution*', [status(thm)], ['10', '153', '154'])).
% 1.30/1.52  thf('190', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.30/1.52      inference('simpl_trail', [status(thm)], ['188', '189'])).
% 1.30/1.52  thf('191', plain, ((v1_relat_1 @ sk_C_1)),
% 1.30/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.52  thf('192', plain, ((v1_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('193', plain, ((v2_funct_1 @ sk_C_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('194', plain,
% 1.30/1.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.30/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.30/1.52      inference('demod', [status(thm)], ['170', '190', '191', '192', '193'])).
% 1.30/1.52  thf('195', plain, ($false), inference('demod', [status(thm)], ['156', '194'])).
% 1.30/1.52  
% 1.30/1.52  % SZS output end Refutation
% 1.30/1.52  
% 1.30/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
