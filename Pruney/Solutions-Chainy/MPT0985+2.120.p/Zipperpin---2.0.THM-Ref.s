%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lIHGGDd3Q

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 857 expanded)
%              Number of leaves         :   48 ( 275 expanded)
%              Depth                    :   21
%              Number of atoms          : 1289 (12867 expanded)
%              Number of equality atoms :   75 ( 544 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
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
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
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
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','48'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','57','58'])).

thf('60',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('61',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('62',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X13 ) )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('63',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('65',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('71',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('72',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['49','60','65','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','74','75'])).

thf('77',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('79',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
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
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','99'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('102',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('104',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','102','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('108',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','101'])).

thf('109',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('114',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('115',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('116',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('118',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('119',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('120',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('121',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['105','112','113','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lIHGGDd3Q
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.72/2.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.72/2.92  % Solved by: fo/fo7.sh
% 2.72/2.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.92  % done 2701 iterations in 2.467s
% 2.72/2.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.72/2.92  % SZS output start Refutation
% 2.72/2.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.72/2.92  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.72/2.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.72/2.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.72/2.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.72/2.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.72/2.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.72/2.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.72/2.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.72/2.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.72/2.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.72/2.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.72/2.92  thf(sk_B_type, type, sk_B: $i > $i).
% 2.72/2.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.72/2.92  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 2.72/2.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.72/2.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.72/2.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.72/2.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.72/2.92  thf(sk_C_type, type, sk_C: $i).
% 2.72/2.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.72/2.92  thf(t31_funct_2, conjecture,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.92       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.72/2.92         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.72/2.92           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.72/2.92           ( m1_subset_1 @
% 2.72/2.92             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.92    (~( ![A:$i,B:$i,C:$i]:
% 2.72/2.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.92          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.72/2.92            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.72/2.92              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.72/2.92              ( m1_subset_1 @
% 2.72/2.92                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.72/2.92    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.72/2.92  thf('0', plain,
% 2.72/2.92      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.72/2.92        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 2.72/2.92        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('1', plain,
% 2.72/2.92      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 2.72/2.92         <= (~
% 2.72/2.92             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 2.72/2.92      inference('split', [status(esa)], ['0'])).
% 2.72/2.92  thf('2', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(cc1_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( v1_relat_1 @ C ) ))).
% 2.72/2.92  thf('3', plain,
% 2.72/2.92      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.72/2.92         ((v1_relat_1 @ X15)
% 2.72/2.92          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.72/2.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.72/2.92  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '3'])).
% 2.72/2.92  thf(dt_k2_funct_1, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.92       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.72/2.92         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.72/2.92  thf('5', plain,
% 2.72/2.92      (![X11 : $i]:
% 2.72/2.92         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.72/2.92          | ~ (v1_funct_1 @ X11)
% 2.72/2.92          | ~ (v1_relat_1 @ X11))),
% 2.72/2.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.92  thf('6', plain,
% 2.72/2.92      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.72/2.92         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.72/2.92      inference('split', [status(esa)], ['0'])).
% 2.72/2.92  thf('7', plain,
% 2.72/2.92      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.72/2.92         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['5', '6'])).
% 2.72/2.92  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('9', plain,
% 2.72/2.92      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.72/2.92      inference('demod', [status(thm)], ['7', '8'])).
% 2.72/2.92  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['4', '9'])).
% 2.72/2.92  thf('11', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('split', [status(esa)], ['0'])).
% 2.72/2.92  thf(d1_funct_2, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.72/2.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.72/2.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.72/2.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_1, axiom,
% 2.72/2.92    (![B:$i,A:$i]:
% 2.72/2.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.92       ( zip_tseitin_0 @ B @ A ) ))).
% 2.72/2.92  thf('12', plain,
% 2.72/2.92      (![X24 : $i, X25 : $i]:
% 2.72/2.92         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.72/2.92  thf('13', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_3, axiom,
% 2.72/2.92    (![C:$i,B:$i,A:$i]:
% 2.72/2.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.72/2.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_5, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.72/2.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.72/2.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.72/2.92  thf('14', plain,
% 2.72/2.92      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.72/2.92         (~ (zip_tseitin_0 @ X29 @ X30)
% 2.72/2.92          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 2.72/2.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.72/2.92  thf('15', plain,
% 2.72/2.92      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.72/2.92        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.72/2.92      inference('sup-', [status(thm)], ['13', '14'])).
% 2.72/2.92  thf('16', plain,
% 2.72/2.92      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 2.72/2.92      inference('sup-', [status(thm)], ['12', '15'])).
% 2.72/2.92  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('18', plain,
% 2.72/2.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.72/2.92         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 2.72/2.92          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 2.72/2.92          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.72/2.92  thf('19', plain,
% 2.72/2.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.72/2.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['17', '18'])).
% 2.72/2.92  thf('20', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(redefinition_k1_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.72/2.92  thf('21', plain,
% 2.72/2.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.72/2.92         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 2.72/2.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.72/2.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.72/2.92  thf('22', plain,
% 2.72/2.92      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.92  thf('23', plain,
% 2.72/2.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.72/2.92        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.72/2.92      inference('demod', [status(thm)], ['19', '22'])).
% 2.72/2.92  thf('24', plain,
% 2.72/2.92      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['16', '23'])).
% 2.72/2.92  thf(t55_funct_1, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.92       ( ( v2_funct_1 @ A ) =>
% 2.72/2.92         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.72/2.92           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.72/2.92  thf('25', plain,
% 2.72/2.92      (![X12 : $i]:
% 2.72/2.92         (~ (v2_funct_1 @ X12)
% 2.72/2.92          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.72/2.92          | ~ (v1_funct_1 @ X12)
% 2.72/2.92          | ~ (v1_relat_1 @ X12))),
% 2.72/2.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.92  thf('26', plain,
% 2.72/2.92      (![X11 : $i]:
% 2.72/2.92         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.72/2.92          | ~ (v1_funct_1 @ X11)
% 2.72/2.92          | ~ (v1_relat_1 @ X11))),
% 2.72/2.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.92  thf('27', plain,
% 2.72/2.92      (![X11 : $i]:
% 2.72/2.92         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.72/2.92          | ~ (v1_funct_1 @ X11)
% 2.72/2.92          | ~ (v1_relat_1 @ X11))),
% 2.72/2.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.92  thf('28', plain,
% 2.72/2.92      (![X12 : $i]:
% 2.72/2.92         (~ (v2_funct_1 @ X12)
% 2.72/2.92          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.72/2.92          | ~ (v1_funct_1 @ X12)
% 2.72/2.92          | ~ (v1_relat_1 @ X12))),
% 2.72/2.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.92  thf(t3_funct_2, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.92       ( ( v1_funct_1 @ A ) & 
% 2.72/2.92         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.72/2.92         ( m1_subset_1 @
% 2.72/2.92           A @ 
% 2.72/2.92           ( k1_zfmisc_1 @
% 2.72/2.92             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.72/2.92  thf('29', plain,
% 2.72/2.92      (![X32 : $i]:
% 2.72/2.92         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 2.72/2.92          | ~ (v1_funct_1 @ X32)
% 2.72/2.92          | ~ (v1_relat_1 @ X32))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.72/2.92  thf('30', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['28', '29'])).
% 2.72/2.92  thf('31', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['27', '30'])).
% 2.72/2.92  thf('32', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['31'])).
% 2.72/2.92  thf('33', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['26', '32'])).
% 2.72/2.92  thf('34', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('35', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92           (k1_relat_1 @ X0))
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0))),
% 2.72/2.92      inference('sup+', [status(thm)], ['25', '34'])).
% 2.72/2.92  thf('36', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.72/2.92             (k1_relat_1 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['35'])).
% 2.72/2.92  thf('37', plain,
% 2.72/2.92      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 2.72/2.92        | ((sk_B_1) = (k1_xboole_0))
% 2.72/2.92        | ~ (v1_relat_1 @ sk_C)
% 2.72/2.92        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.92        | ~ (v2_funct_1 @ sk_C))),
% 2.72/2.92      inference('sup+', [status(thm)], ['24', '36'])).
% 2.72/2.92  thf('38', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(redefinition_k2_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.72/2.92  thf('39', plain,
% 2.72/2.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.72/2.92         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 2.72/2.92          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.72/2.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.92  thf('40', plain,
% 2.72/2.92      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['38', '39'])).
% 2.72/2.92  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['40', '41'])).
% 2.72/2.92  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '3'])).
% 2.72/2.92  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('46', plain,
% 2.72/2.92      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 2.72/2.92        | ((sk_B_1) = (k1_xboole_0)))),
% 2.72/2.92      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 2.72/2.92  thf('47', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('split', [status(esa)], ['0'])).
% 2.72/2.92  thf('48', plain,
% 2.72/2.92      ((((sk_B_1) = (k1_xboole_0)))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['46', '47'])).
% 2.72/2.92  thf('49', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['11', '48'])).
% 2.72/2.92  thf(t7_xboole_0, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.72/2.92          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.72/2.92  thf('50', plain,
% 2.72/2.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.72/2.92  thf('51', plain,
% 2.72/2.92      ((((sk_B_1) = (k1_xboole_0)))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['46', '47'])).
% 2.72/2.92  thf('52', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(t5_subset, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.72/2.92          ( v1_xboole_0 @ C ) ) ))).
% 2.72/2.92  thf('53', plain,
% 2.72/2.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.72/2.92         (~ (r2_hidden @ X8 @ X9)
% 2.72/2.92          | ~ (v1_xboole_0 @ X10)
% 2.72/2.92          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t5_subset])).
% 2.72/2.92  thf('54', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.72/2.92          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['52', '53'])).
% 2.72/2.92  thf('55', plain,
% 2.72/2.92      ((![X0 : $i]:
% 2.72/2.92          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 2.72/2.92           | ~ (r2_hidden @ X0 @ sk_C)))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['51', '54'])).
% 2.72/2.92  thf(t113_zfmisc_1, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.72/2.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.72/2.92  thf('56', plain,
% 2.72/2.92      (![X6 : $i, X7 : $i]:
% 2.72/2.92         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.72/2.92  thf('57', plain,
% 2.72/2.92      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['56'])).
% 2.72/2.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.72/2.92  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.72/2.92  thf('59', plain,
% 2.72/2.92      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['55', '57', '58'])).
% 2.72/2.92  thf('60', plain,
% 2.72/2.92      ((((sk_C) = (k1_xboole_0)))
% 2.72/2.92         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['50', '59'])).
% 2.72/2.92  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.72/2.92  thf('61', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.72/2.92  thf(t67_funct_1, axiom,
% 2.72/2.92    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.72/2.92  thf('62', plain,
% 2.72/2.92      (![X13 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X13)) = (k6_relat_1 @ X13))),
% 2.72/2.92      inference('cnf', [status(esa)], [t67_funct_1])).
% 2.72/2.92  thf('63', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 2.72/2.92      inference('sup+', [status(thm)], ['61', '62'])).
% 2.72/2.92  thf('64', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.72/2.92  thf('65', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('demod', [status(thm)], ['63', '64'])).
% 2.72/2.92  thf(t60_relat_1, axiom,
% 2.72/2.92    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.72/2.92     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.72/2.92  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.72/2.92  thf(t4_funct_2, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.72/2.92       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.72/2.92         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 2.72/2.92           ( m1_subset_1 @
% 2.72/2.92             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 2.72/2.92  thf('67', plain,
% 2.72/2.92      (![X33 : $i, X34 : $i]:
% 2.72/2.92         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 2.72/2.92          | (v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ X34)
% 2.72/2.92          | ~ (v1_funct_1 @ X33)
% 2.72/2.92          | ~ (v1_relat_1 @ X33))),
% 2.72/2.92      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.72/2.92  thf('68', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.72/2.92          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.72/2.92          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['66', '67'])).
% 2.72/2.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.72/2.92  thf('69', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.72/2.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.72/2.92  thf(t45_ordinal1, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 2.72/2.92       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 2.72/2.92  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [t45_ordinal1])).
% 2.72/2.92  thf('71', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [t45_ordinal1])).
% 2.72/2.92  thf('72', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.72/2.92  thf('73', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.72/2.92      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 2.72/2.92  thf('74', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 2.72/2.92      inference('demod', [status(thm)], ['49', '60', '65', '73'])).
% 2.72/2.92  thf('75', plain,
% 2.72/2.92      (~
% 2.72/2.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 2.72/2.92       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)) | 
% 2.72/2.92       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.72/2.92      inference('split', [status(esa)], ['0'])).
% 2.72/2.92  thf('76', plain,
% 2.72/2.92      (~
% 2.72/2.92       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 2.72/2.92      inference('sat_resolution*', [status(thm)], ['10', '74', '75'])).
% 2.72/2.92  thf('77', plain,
% 2.72/2.92      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 2.72/2.92  thf('78', plain,
% 2.72/2.92      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['16', '23'])).
% 2.72/2.92  thf('79', plain,
% 2.72/2.92      (![X12 : $i]:
% 2.72/2.92         (~ (v2_funct_1 @ X12)
% 2.72/2.92          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.72/2.92          | ~ (v1_funct_1 @ X12)
% 2.72/2.92          | ~ (v1_relat_1 @ X12))),
% 2.72/2.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.92  thf('80', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['40', '41'])).
% 2.72/2.92  thf('81', plain,
% 2.72/2.92      (![X11 : $i]:
% 2.72/2.92         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.72/2.92          | ~ (v1_funct_1 @ X11)
% 2.72/2.92          | ~ (v1_relat_1 @ X11))),
% 2.72/2.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.92  thf('82', plain,
% 2.72/2.92      (![X11 : $i]:
% 2.72/2.92         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.72/2.92          | ~ (v1_funct_1 @ X11)
% 2.72/2.92          | ~ (v1_relat_1 @ X11))),
% 2.72/2.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.92  thf('83', plain,
% 2.72/2.92      (![X12 : $i]:
% 2.72/2.92         (~ (v2_funct_1 @ X12)
% 2.72/2.92          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.72/2.92          | ~ (v1_funct_1 @ X12)
% 2.72/2.92          | ~ (v1_relat_1 @ X12))),
% 2.72/2.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.92  thf('84', plain,
% 2.72/2.92      (![X32 : $i]:
% 2.72/2.92         ((m1_subset_1 @ X32 @ 
% 2.72/2.92           (k1_zfmisc_1 @ 
% 2.72/2.92            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.72/2.92          | ~ (v1_funct_1 @ X32)
% 2.72/2.92          | ~ (v1_relat_1 @ X32))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.72/2.92  thf('85', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.72/2.92           (k1_zfmisc_1 @ 
% 2.72/2.92            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['83', '84'])).
% 2.72/2.92  thf('86', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.72/2.92             (k1_zfmisc_1 @ 
% 2.72/2.92              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.72/2.92               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['82', '85'])).
% 2.72/2.92  thf('87', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.72/2.92           (k1_zfmisc_1 @ 
% 2.72/2.92            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['86'])).
% 2.72/2.92  thf('88', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.72/2.92             (k1_zfmisc_1 @ 
% 2.72/2.92              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.72/2.92               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['81', '87'])).
% 2.72/2.92  thf('89', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.72/2.92           (k1_zfmisc_1 @ 
% 2.72/2.92            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.72/2.92          | ~ (v2_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_funct_1 @ X0)
% 2.72/2.92          | ~ (v1_relat_1 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['88'])).
% 2.72/2.92  thf('90', plain,
% 2.72/2.92      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92         (k1_zfmisc_1 @ 
% 2.72/2.92          (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.72/2.92        | ~ (v1_relat_1 @ sk_C)
% 2.72/2.92        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.92        | ~ (v2_funct_1 @ sk_C))),
% 2.72/2.92      inference('sup+', [status(thm)], ['80', '89'])).
% 2.72/2.92  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '3'])).
% 2.72/2.92  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('94', plain,
% 2.72/2.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92        (k1_zfmisc_1 @ 
% 2.72/2.92         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.72/2.92      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 2.72/2.92  thf('95', plain,
% 2.72/2.92      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C))))
% 2.72/2.92        | ~ (v1_relat_1 @ sk_C)
% 2.72/2.92        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.92        | ~ (v2_funct_1 @ sk_C))),
% 2.72/2.92      inference('sup+', [status(thm)], ['79', '94'])).
% 2.72/2.92  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '3'])).
% 2.72/2.92  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('99', plain,
% 2.72/2.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C))))),
% 2.72/2.92      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 2.72/2.92  thf('100', plain,
% 2.72/2.92      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.72/2.92        | ((sk_B_1) = (k1_xboole_0)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['78', '99'])).
% 2.72/2.92  thf('101', plain,
% 2.72/2.92      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.72/2.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.72/2.92      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 2.72/2.92  thf('102', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.72/2.92      inference('clc', [status(thm)], ['100', '101'])).
% 2.72/2.92  thf('103', plain,
% 2.72/2.92      (![X6 : $i, X7 : $i]:
% 2.72/2.92         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.72/2.92  thf('104', plain,
% 2.72/2.92      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['103'])).
% 2.72/2.92  thf('105', plain,
% 2.72/2.92      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.72/2.92      inference('demod', [status(thm)], ['77', '102', '104'])).
% 2.72/2.92  thf('106', plain,
% 2.72/2.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.72/2.92  thf('107', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.72/2.92          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['52', '53'])).
% 2.72/2.92  thf('108', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.72/2.92      inference('clc', [status(thm)], ['100', '101'])).
% 2.72/2.92  thf('109', plain,
% 2.72/2.92      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['56'])).
% 2.72/2.92  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.72/2.92  thf('111', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 2.72/2.92      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 2.72/2.92  thf('112', plain, (((sk_C) = (k1_xboole_0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['106', '111'])).
% 2.72/2.92  thf('113', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('demod', [status(thm)], ['63', '64'])).
% 2.72/2.92  thf('114', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.72/2.92  thf('115', plain,
% 2.72/2.92      (![X32 : $i]:
% 2.72/2.92         ((m1_subset_1 @ X32 @ 
% 2.72/2.92           (k1_zfmisc_1 @ 
% 2.72/2.92            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.72/2.92          | ~ (v1_funct_1 @ X32)
% 2.72/2.92          | ~ (v1_relat_1 @ X32))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.72/2.92  thf('116', plain,
% 2.72/2.92      (((m1_subset_1 @ k1_xboole_0 @ 
% 2.72/2.92         (k1_zfmisc_1 @ 
% 2.72/2.92          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))
% 2.72/2.92        | ~ (v1_relat_1 @ k1_xboole_0)
% 2.72/2.92        | ~ (v1_funct_1 @ k1_xboole_0))),
% 2.72/2.92      inference('sup+', [status(thm)], ['114', '115'])).
% 2.72/2.92  thf('117', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.72/2.92  thf('118', plain,
% 2.72/2.92      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['103'])).
% 2.72/2.92  thf('119', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [t45_ordinal1])).
% 2.72/2.92  thf('120', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.72/2.92      inference('cnf', [status(esa)], [t45_ordinal1])).
% 2.72/2.92  thf('121', plain,
% 2.72/2.92      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.72/2.92      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 2.72/2.92  thf('122', plain, ($false),
% 2.72/2.92      inference('demod', [status(thm)], ['105', '112', '113', '121'])).
% 2.72/2.92  
% 2.72/2.92  % SZS output end Refutation
% 2.72/2.92  
% 2.72/2.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
