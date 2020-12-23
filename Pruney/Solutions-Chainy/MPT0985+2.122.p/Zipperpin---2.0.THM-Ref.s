%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.giVCFKdmva

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:44 EST 2020

% Result     : Theorem 3.88s
% Output     : Refutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  219 (1513 expanded)
%              Number of leaves         :   38 ( 455 expanded)
%              Depth                    :   25
%              Number of atoms          : 1808 (23531 expanded)
%              Number of equality atoms :  116 (1057 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
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

thf('64',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('67',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('69',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('71',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('80',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','79','82'])).

thf('84',plain,
    ( ( ~ ( v2_funct_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','58','59','60','61'])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('96',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('104',plain,(
    ! [X25: $i] :
      ( zip_tseitin_0 @ X25 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('106',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['102','108'])).

thf('110',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['63','94','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','110','111'])).

thf('113',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','112'])).

thf('114',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('122',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['120','130'])).

thf('132',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('133',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('136',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ X0 @ sk_B @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['134','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('143',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['141','146'])).

thf('148',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['133','147'])).

thf('149',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('151',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('158',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('165',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','110','111'])).

thf('167',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['165','166'])).

thf('168',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['156','167'])).

thf('169',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['168','172'])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174','175','176','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['113','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.giVCFKdmva
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.88/4.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.88/4.09  % Solved by: fo/fo7.sh
% 3.88/4.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.88/4.09  % done 3135 iterations in 3.635s
% 3.88/4.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.88/4.09  % SZS output start Refutation
% 3.88/4.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.88/4.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.88/4.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.88/4.09  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.88/4.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.88/4.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.88/4.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.88/4.09  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.88/4.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.88/4.09  thf(sk_A_type, type, sk_A: $i).
% 3.88/4.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.88/4.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.88/4.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.88/4.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.88/4.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.88/4.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.88/4.09  thf(sk_B_type, type, sk_B: $i).
% 3.88/4.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.88/4.09  thf(sk_C_type, type, sk_C: $i).
% 3.88/4.09  thf(t31_funct_2, conjecture,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.88/4.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.88/4.09       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.88/4.09         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.88/4.09           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.88/4.09           ( m1_subset_1 @
% 3.88/4.09             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.88/4.09  thf(zf_stmt_0, negated_conjecture,
% 3.88/4.09    (~( ![A:$i,B:$i,C:$i]:
% 3.88/4.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.88/4.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.88/4.09          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.88/4.09            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.88/4.09              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.88/4.09              ( m1_subset_1 @
% 3.88/4.09                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.88/4.09    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.88/4.09  thf('0', plain,
% 3.88/4.09      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.88/4.09        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.88/4.09        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('1', plain,
% 3.88/4.09      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.88/4.09         <= (~
% 3.88/4.09             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf('2', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf(cc1_relset_1, axiom,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.88/4.09       ( v1_relat_1 @ C ) ))).
% 3.88/4.09  thf('3', plain,
% 3.88/4.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.88/4.09         ((v1_relat_1 @ X16)
% 3.88/4.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.88/4.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.88/4.09  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 3.88/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.88/4.09  thf(dt_k2_funct_1, axiom,
% 3.88/4.09    (![A:$i]:
% 3.88/4.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.88/4.09       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.88/4.09         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.88/4.09  thf('5', plain,
% 3.88/4.09      (![X14 : $i]:
% 3.88/4.09         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.88/4.09          | ~ (v1_funct_1 @ X14)
% 3.88/4.09          | ~ (v1_relat_1 @ X14))),
% 3.88/4.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.88/4.09  thf('6', plain,
% 3.88/4.09      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.88/4.09         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf('7', plain,
% 3.88/4.09      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 3.88/4.09         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['5', '6'])).
% 3.88/4.09  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('9', plain,
% 3.88/4.09      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.88/4.09      inference('demod', [status(thm)], ['7', '8'])).
% 3.88/4.09  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['4', '9'])).
% 3.88/4.09  thf('11', plain,
% 3.88/4.09      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf(d1_funct_2, axiom,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.88/4.09       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.88/4.09           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.88/4.09             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.88/4.09         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.88/4.09           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.88/4.09             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.88/4.09  thf(zf_stmt_1, axiom,
% 3.88/4.09    (![B:$i,A:$i]:
% 3.88/4.09     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.88/4.09       ( zip_tseitin_0 @ B @ A ) ))).
% 3.88/4.09  thf('12', plain,
% 3.88/4.09      (![X25 : $i, X26 : $i]:
% 3.88/4.09         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.88/4.09  thf('13', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.88/4.09  thf(zf_stmt_3, axiom,
% 3.88/4.09    (![C:$i,B:$i,A:$i]:
% 3.88/4.09     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.88/4.09       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.88/4.09  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.88/4.09  thf(zf_stmt_5, axiom,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.88/4.09       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.88/4.09         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.88/4.09           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.88/4.09             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.88/4.09  thf('14', plain,
% 3.88/4.09      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.88/4.09         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.88/4.09          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.88/4.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.88/4.09  thf('15', plain,
% 3.88/4.09      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['13', '14'])).
% 3.88/4.09  thf('16', plain,
% 3.88/4.09      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['12', '15'])).
% 3.88/4.09  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('18', plain,
% 3.88/4.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.88/4.09         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.88/4.09          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 3.88/4.09          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.88/4.09  thf('19', plain,
% 3.88/4.09      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 3.88/4.09        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['17', '18'])).
% 3.88/4.09  thf('20', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf(redefinition_k1_relset_1, axiom,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.88/4.09       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.88/4.09  thf('21', plain,
% 3.88/4.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.88/4.09         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.88/4.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.88/4.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.88/4.09  thf('22', plain,
% 3.88/4.09      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.88/4.09      inference('sup-', [status(thm)], ['20', '21'])).
% 3.88/4.09  thf('23', plain,
% 3.88/4.09      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['19', '22'])).
% 3.88/4.09  thf('24', plain,
% 3.88/4.09      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['16', '23'])).
% 3.88/4.09  thf(t55_funct_1, axiom,
% 3.88/4.09    (![A:$i]:
% 3.88/4.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.88/4.09       ( ( v2_funct_1 @ A ) =>
% 3.88/4.09         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.88/4.09           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.88/4.09  thf('25', plain,
% 3.88/4.09      (![X15 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X15)
% 3.88/4.09          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 3.88/4.09          | ~ (v1_funct_1 @ X15)
% 3.88/4.09          | ~ (v1_relat_1 @ X15))),
% 3.88/4.09      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.88/4.09  thf('26', plain,
% 3.88/4.09      (![X14 : $i]:
% 3.88/4.09         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.88/4.09          | ~ (v1_funct_1 @ X14)
% 3.88/4.09          | ~ (v1_relat_1 @ X14))),
% 3.88/4.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.88/4.09  thf('27', plain,
% 3.88/4.09      (![X14 : $i]:
% 3.88/4.09         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 3.88/4.09          | ~ (v1_funct_1 @ X14)
% 3.88/4.09          | ~ (v1_relat_1 @ X14))),
% 3.88/4.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.88/4.09  thf('28', plain,
% 3.88/4.09      (![X15 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X15)
% 3.88/4.09          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 3.88/4.09          | ~ (v1_funct_1 @ X15)
% 3.88/4.09          | ~ (v1_relat_1 @ X15))),
% 3.88/4.09      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.88/4.09  thf(t3_funct_2, axiom,
% 3.88/4.09    (![A:$i]:
% 3.88/4.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.88/4.09       ( ( v1_funct_1 @ A ) & 
% 3.88/4.09         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.88/4.09         ( m1_subset_1 @
% 3.88/4.09           A @ 
% 3.88/4.09           ( k1_zfmisc_1 @
% 3.88/4.09             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.88/4.09  thf('29', plain,
% 3.88/4.09      (![X33 : $i]:
% 3.88/4.09         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 3.88/4.09          | ~ (v1_funct_1 @ X33)
% 3.88/4.09          | ~ (v1_relat_1 @ X33))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.88/4.09  thf('30', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['28', '29'])).
% 3.88/4.09  thf('31', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['27', '30'])).
% 3.88/4.09  thf('32', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['31'])).
% 3.88/4.09  thf('33', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['26', '32'])).
% 3.88/4.09  thf('34', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['33'])).
% 3.88/4.09  thf('35', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09           (k1_relat_1 @ X0))
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0))),
% 3.88/4.09      inference('sup+', [status(thm)], ['25', '34'])).
% 3.88/4.09  thf('36', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.88/4.09             (k1_relat_1 @ X0)))),
% 3.88/4.09      inference('simplify', [status(thm)], ['35'])).
% 3.88/4.09  thf('37', plain,
% 3.88/4.09      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 3.88/4.09        | ((sk_B) = (k1_xboole_0))
% 3.88/4.09        | ~ (v1_relat_1 @ sk_C)
% 3.88/4.09        | ~ (v1_funct_1 @ sk_C)
% 3.88/4.09        | ~ (v2_funct_1 @ sk_C))),
% 3.88/4.09      inference('sup+', [status(thm)], ['24', '36'])).
% 3.88/4.09  thf('38', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf(redefinition_k2_relset_1, axiom,
% 3.88/4.09    (![A:$i,B:$i,C:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.88/4.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.88/4.09  thf('39', plain,
% 3.88/4.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.88/4.09         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.88/4.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.88/4.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.88/4.09  thf('40', plain,
% 3.88/4.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.88/4.09      inference('sup-', [status(thm)], ['38', '39'])).
% 3.88/4.09  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.88/4.09      inference('sup+', [status(thm)], ['40', '41'])).
% 3.88/4.09  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 3.88/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.88/4.09  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('46', plain,
% 3.88/4.09      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.88/4.09        | ((sk_B) = (k1_xboole_0)))),
% 3.88/4.09      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 3.88/4.09  thf('47', plain,
% 3.88/4.09      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf('48', plain,
% 3.88/4.09      ((((sk_B) = (k1_xboole_0)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['46', '47'])).
% 3.88/4.09  thf('49', plain,
% 3.88/4.09      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['11', '48'])).
% 3.88/4.09  thf('50', plain,
% 3.88/4.09      ((((sk_B) = (k1_xboole_0)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['46', '47'])).
% 3.88/4.09  thf('51', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf(t3_subset, axiom,
% 3.88/4.09    (![A:$i,B:$i]:
% 3.88/4.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.88/4.09  thf('52', plain,
% 3.88/4.09      (![X8 : $i, X9 : $i]:
% 3.88/4.09         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.88/4.09  thf('53', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.88/4.09      inference('sup-', [status(thm)], ['51', '52'])).
% 3.88/4.09  thf(d10_xboole_0, axiom,
% 3.88/4.09    (![A:$i,B:$i]:
% 3.88/4.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.88/4.09  thf('54', plain,
% 3.88/4.09      (![X0 : $i, X2 : $i]:
% 3.88/4.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.88/4.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.09  thf('55', plain,
% 3.88/4.09      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 3.88/4.09        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['53', '54'])).
% 3.88/4.09  thf('56', plain,
% 3.88/4.09      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 3.88/4.09         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['50', '55'])).
% 3.88/4.09  thf(t113_zfmisc_1, axiom,
% 3.88/4.09    (![A:$i,B:$i]:
% 3.88/4.09     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.88/4.09       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.88/4.09  thf('57', plain,
% 3.88/4.09      (![X5 : $i, X6 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.88/4.09  thf('58', plain,
% 3.88/4.09      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['57'])).
% 3.88/4.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.88/4.09  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.88/4.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.88/4.09  thf('60', plain,
% 3.88/4.09      ((((sk_B) = (k1_xboole_0)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['46', '47'])).
% 3.88/4.09  thf('61', plain,
% 3.88/4.09      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['57'])).
% 3.88/4.09  thf('62', plain,
% 3.88/4.09      ((((k1_xboole_0) = (sk_C)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 3.88/4.09  thf('63', plain,
% 3.88/4.09      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['49', '62'])).
% 3.88/4.09  thf('64', plain,
% 3.88/4.09      ((((k1_xboole_0) = (sk_C)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 3.88/4.09  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('66', plain,
% 3.88/4.09      (((v1_funct_1 @ k1_xboole_0))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['64', '65'])).
% 3.88/4.09  thf(t60_relat_1, axiom,
% 3.88/4.09    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.88/4.09     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.88/4.09  thf('67', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.88/4.09  thf('68', plain,
% 3.88/4.09      (![X14 : $i]:
% 3.88/4.09         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.88/4.09          | ~ (v1_funct_1 @ X14)
% 3.88/4.09          | ~ (v1_relat_1 @ X14))),
% 3.88/4.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.88/4.09  thf('69', plain,
% 3.88/4.09      (![X14 : $i]:
% 3.88/4.09         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 3.88/4.09          | ~ (v1_funct_1 @ X14)
% 3.88/4.09          | ~ (v1_relat_1 @ X14))),
% 3.88/4.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.88/4.09  thf('70', plain,
% 3.88/4.09      (![X15 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X15)
% 3.88/4.09          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 3.88/4.09          | ~ (v1_funct_1 @ X15)
% 3.88/4.09          | ~ (v1_relat_1 @ X15))),
% 3.88/4.09      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.88/4.09  thf('71', plain,
% 3.88/4.09      (![X33 : $i]:
% 3.88/4.09         ((m1_subset_1 @ X33 @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 3.88/4.09          | ~ (v1_funct_1 @ X33)
% 3.88/4.09          | ~ (v1_relat_1 @ X33))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.88/4.09  thf('72', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['70', '71'])).
% 3.88/4.09  thf('73', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09             (k1_zfmisc_1 @ 
% 3.88/4.09              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 3.88/4.09               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['69', '72'])).
% 3.88/4.09  thf('74', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['73'])).
% 3.88/4.09  thf('75', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09             (k1_zfmisc_1 @ 
% 3.88/4.09              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 3.88/4.09               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['68', '74'])).
% 3.88/4.09  thf('76', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['75'])).
% 3.88/4.09  thf('77', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 3.88/4.09         (k1_zfmisc_1 @ 
% 3.88/4.09          (k2_zfmisc_1 @ k1_xboole_0 @ 
% 3.88/4.09           (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 3.88/4.09        | ~ (v1_relat_1 @ k1_xboole_0)
% 3.88/4.09        | ~ (v1_funct_1 @ k1_xboole_0)
% 3.88/4.09        | ~ (v2_funct_1 @ k1_xboole_0))),
% 3.88/4.09      inference('sup+', [status(thm)], ['67', '76'])).
% 3.88/4.09  thf('78', plain,
% 3.88/4.09      (![X5 : $i, X6 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.88/4.09  thf('79', plain,
% 3.88/4.09      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['78'])).
% 3.88/4.09  thf(t4_subset_1, axiom,
% 3.88/4.09    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.88/4.09  thf('80', plain,
% 3.88/4.09      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.88/4.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.88/4.09  thf('81', plain,
% 3.88/4.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.88/4.09         ((v1_relat_1 @ X16)
% 3.88/4.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.88/4.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.88/4.09  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.88/4.09      inference('sup-', [status(thm)], ['80', '81'])).
% 3.88/4.09  thf('83', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.88/4.09        | ~ (v1_funct_1 @ k1_xboole_0)
% 3.88/4.09        | ~ (v2_funct_1 @ k1_xboole_0))),
% 3.88/4.09      inference('demod', [status(thm)], ['77', '79', '82'])).
% 3.88/4.09  thf('84', plain,
% 3.88/4.09      (((~ (v2_funct_1 @ k1_xboole_0)
% 3.88/4.09         | (m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 3.88/4.09            (k1_zfmisc_1 @ k1_xboole_0))))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['66', '83'])).
% 3.88/4.09  thf('85', plain,
% 3.88/4.09      ((((k1_xboole_0) = (sk_C)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['56', '58', '59', '60', '61'])).
% 3.88/4.09  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('87', plain,
% 3.88/4.09      (((v2_funct_1 @ k1_xboole_0))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['85', '86'])).
% 3.88/4.09  thf('88', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['84', '87'])).
% 3.88/4.09  thf('89', plain,
% 3.88/4.09      (![X8 : $i, X9 : $i]:
% 3.88/4.09         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.88/4.09  thf('90', plain,
% 3.88/4.09      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['88', '89'])).
% 3.88/4.09  thf('91', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.88/4.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.88/4.09  thf('92', plain,
% 3.88/4.09      (![X0 : $i, X2 : $i]:
% 3.88/4.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.88/4.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.09  thf('93', plain,
% 3.88/4.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['91', '92'])).
% 3.88/4.09  thf('94', plain,
% 3.88/4.09      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 3.88/4.09         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['90', '93'])).
% 3.88/4.09  thf('95', plain,
% 3.88/4.09      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.88/4.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.88/4.09  thf('96', plain,
% 3.88/4.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.88/4.09         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.88/4.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.88/4.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.88/4.09  thf('97', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.88/4.09      inference('sup-', [status(thm)], ['95', '96'])).
% 3.88/4.09  thf('98', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.88/4.09  thf('99', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('demod', [status(thm)], ['97', '98'])).
% 3.88/4.09  thf('100', plain,
% 3.88/4.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.88/4.09         (((X27) != (k1_relset_1 @ X27 @ X28 @ X29))
% 3.88/4.09          | (v1_funct_2 @ X29 @ X27 @ X28)
% 3.88/4.09          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.88/4.09  thf('101', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         (((X1) != (k1_xboole_0))
% 3.88/4.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.88/4.09          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.88/4.09      inference('sup-', [status(thm)], ['99', '100'])).
% 3.88/4.09  thf('102', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.88/4.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['101'])).
% 3.88/4.09  thf('103', plain,
% 3.88/4.09      (![X25 : $i, X26 : $i]:
% 3.88/4.09         ((zip_tseitin_0 @ X25 @ X26) | ((X26) != (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.88/4.09  thf('104', plain, (![X25 : $i]: (zip_tseitin_0 @ X25 @ k1_xboole_0)),
% 3.88/4.09      inference('simplify', [status(thm)], ['103'])).
% 3.88/4.09  thf('105', plain,
% 3.88/4.09      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.88/4.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.88/4.09  thf('106', plain,
% 3.88/4.09      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.88/4.09         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.88/4.09          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.88/4.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.88/4.09  thf('107', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.88/4.09      inference('sup-', [status(thm)], ['105', '106'])).
% 3.88/4.09  thf('108', plain,
% 3.88/4.09      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.88/4.09      inference('sup-', [status(thm)], ['104', '107'])).
% 3.88/4.09  thf('109', plain,
% 3.88/4.09      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.88/4.09      inference('demod', [status(thm)], ['102', '108'])).
% 3.88/4.09  thf('110', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.88/4.09      inference('demod', [status(thm)], ['63', '94', '109'])).
% 3.88/4.09  thf('111', plain,
% 3.88/4.09      (~
% 3.88/4.09       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 3.88/4.09       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 3.88/4.09       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf('112', plain,
% 3.88/4.09      (~
% 3.88/4.09       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.88/4.09      inference('sat_resolution*', [status(thm)], ['10', '110', '111'])).
% 3.88/4.09  thf('113', plain,
% 3.88/4.09      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.88/4.09      inference('simpl_trail', [status(thm)], ['1', '112'])).
% 3.88/4.09  thf('114', plain,
% 3.88/4.09      (![X25 : $i, X26 : $i]:
% 3.88/4.09         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.88/4.09  thf('115', plain,
% 3.88/4.09      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['57'])).
% 3.88/4.09  thf('116', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.88/4.09      inference('sup+', [status(thm)], ['114', '115'])).
% 3.88/4.09  thf('117', plain,
% 3.88/4.09      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['13', '14'])).
% 3.88/4.09  thf('118', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.88/4.09          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['116', '117'])).
% 3.88/4.09  thf('119', plain,
% 3.88/4.09      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['19', '22'])).
% 3.88/4.09  thf('120', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.88/4.09          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['118', '119'])).
% 3.88/4.09  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.88/4.09      inference('sup+', [status(thm)], ['40', '41'])).
% 3.88/4.09  thf('122', plain,
% 3.88/4.09      (![X33 : $i]:
% 3.88/4.09         ((m1_subset_1 @ X33 @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 3.88/4.09          | ~ (v1_funct_1 @ X33)
% 3.88/4.09          | ~ (v1_relat_1 @ X33))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.88/4.09  thf('123', plain,
% 3.88/4.09      (((m1_subset_1 @ sk_C @ 
% 3.88/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 3.88/4.09        | ~ (v1_relat_1 @ sk_C)
% 3.88/4.09        | ~ (v1_funct_1 @ sk_C))),
% 3.88/4.09      inference('sup+', [status(thm)], ['121', '122'])).
% 3.88/4.09  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 3.88/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.88/4.09  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('126', plain,
% 3.88/4.09      ((m1_subset_1 @ sk_C @ 
% 3.88/4.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 3.88/4.09      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.88/4.09  thf('127', plain,
% 3.88/4.09      (![X8 : $i, X9 : $i]:
% 3.88/4.09         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.88/4.09  thf('128', plain,
% 3.88/4.09      ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 3.88/4.09      inference('sup-', [status(thm)], ['126', '127'])).
% 3.88/4.09  thf('129', plain,
% 3.88/4.09      (![X0 : $i, X2 : $i]:
% 3.88/4.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.88/4.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.09  thf('130', plain,
% 3.88/4.09      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B) @ sk_C)
% 3.88/4.09        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B) = (sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['128', '129'])).
% 3.88/4.09  thf('131', plain,
% 3.88/4.09      ((~ (r1_tarski @ k1_xboole_0 @ sk_C)
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C))
% 3.88/4.09        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B) = (sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['120', '130'])).
% 3.88/4.09  thf('132', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.88/4.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.88/4.09  thf('133', plain,
% 3.88/4.09      ((((sk_A) = (k1_relat_1 @ sk_C))
% 3.88/4.09        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B) = (sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['131', '132'])).
% 3.88/4.09  thf('134', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.88/4.09          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['118', '119'])).
% 3.88/4.09  thf('135', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.88/4.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.09  thf('136', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.88/4.09      inference('simplify', [status(thm)], ['135'])).
% 3.88/4.09  thf('137', plain,
% 3.88/4.09      (![X8 : $i, X10 : $i]:
% 3.88/4.09         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.88/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.88/4.09  thf('138', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.88/4.09      inference('sup-', [status(thm)], ['136', '137'])).
% 3.88/4.09  thf('139', plain,
% 3.88/4.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.88/4.09         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.88/4.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.88/4.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.88/4.09  thf('140', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.88/4.09           = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['138', '139'])).
% 3.88/4.09  thf('141', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_relset_1 @ X0 @ sk_B @ k1_xboole_0)
% 3.88/4.09            = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.88/4.09          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['134', '140'])).
% 3.88/4.09  thf('142', plain,
% 3.88/4.09      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.88/4.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.88/4.09  thf('143', plain,
% 3.88/4.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.88/4.09         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.88/4.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.88/4.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.88/4.09  thf('144', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 3.88/4.09      inference('sup-', [status(thm)], ['142', '143'])).
% 3.88/4.09  thf('145', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.88/4.09  thf('146', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i]:
% 3.88/4.09         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.88/4.09      inference('demod', [status(thm)], ['144', '145'])).
% 3.88/4.09  thf('147', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k1_xboole_0) = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.88/4.09          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['141', '146'])).
% 3.88/4.09  thf('148', plain,
% 3.88/4.09      ((((k1_xboole_0) = (k2_relat_1 @ sk_C))
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C))
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup+', [status(thm)], ['133', '147'])).
% 3.88/4.09  thf('149', plain,
% 3.88/4.09      ((((sk_A) = (k1_relat_1 @ sk_C)) | ((k1_xboole_0) = (k2_relat_1 @ sk_C)))),
% 3.88/4.09      inference('simplify', [status(thm)], ['148'])).
% 3.88/4.09  thf('150', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['75'])).
% 3.88/4.09  thf('151', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09         (k1_zfmisc_1 @ 
% 3.88/4.09          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C))
% 3.88/4.09        | ~ (v1_relat_1 @ sk_C)
% 3.88/4.09        | ~ (v1_funct_1 @ sk_C)
% 3.88/4.09        | ~ (v2_funct_1 @ sk_C))),
% 3.88/4.09      inference('sup+', [status(thm)], ['149', '150'])).
% 3.88/4.09  thf('152', plain,
% 3.88/4.09      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['78'])).
% 3.88/4.09  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 3.88/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.88/4.09  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('156', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 3.88/4.09  thf('157', plain,
% 3.88/4.09      (![X25 : $i, X26 : $i]:
% 3.88/4.09         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.88/4.09  thf('158', plain,
% 3.88/4.09      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['78'])).
% 3.88/4.09  thf('159', plain,
% 3.88/4.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.88/4.09      inference('sup+', [status(thm)], ['157', '158'])).
% 3.88/4.09  thf('160', plain,
% 3.88/4.09      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['13', '14'])).
% 3.88/4.09  thf('161', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 3.88/4.09          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 3.88/4.09      inference('sup-', [status(thm)], ['159', '160'])).
% 3.88/4.09  thf('162', plain,
% 3.88/4.09      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('demod', [status(thm)], ['19', '22'])).
% 3.88/4.09  thf('163', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 3.88/4.09          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('sup-', [status(thm)], ['161', '162'])).
% 3.88/4.09  thf('164', plain,
% 3.88/4.09      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.88/4.09         <= (~
% 3.88/4.09             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.88/4.09      inference('split', [status(esa)], ['0'])).
% 3.88/4.09  thf('165', plain,
% 3.88/4.09      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.88/4.09         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 3.88/4.09         <= (~
% 3.88/4.09             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.88/4.09      inference('sup-', [status(thm)], ['163', '164'])).
% 3.88/4.09  thf('166', plain,
% 3.88/4.09      (~
% 3.88/4.09       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.88/4.09      inference('sat_resolution*', [status(thm)], ['10', '110', '111'])).
% 3.88/4.09  thf('167', plain,
% 3.88/4.09      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.88/4.09        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.88/4.09      inference('simpl_trail', [status(thm)], ['165', '166'])).
% 3.88/4.09  thf('168', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 3.88/4.09      inference('clc', [status(thm)], ['156', '167'])).
% 3.88/4.09  thf('169', plain,
% 3.88/4.09      (![X15 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X15)
% 3.88/4.09          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 3.88/4.09          | ~ (v1_funct_1 @ X15)
% 3.88/4.09          | ~ (v1_relat_1 @ X15))),
% 3.88/4.09      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.88/4.09  thf('170', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ 
% 3.88/4.09            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0))),
% 3.88/4.09      inference('simplify', [status(thm)], ['75'])).
% 3.88/4.09  thf('171', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v2_funct_1 @ X0))),
% 3.88/4.09      inference('sup+', [status(thm)], ['169', '170'])).
% 3.88/4.09  thf('172', plain,
% 3.88/4.09      (![X0 : $i]:
% 3.88/4.09         (~ (v2_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_funct_1 @ X0)
% 3.88/4.09          | ~ (v1_relat_1 @ X0)
% 3.88/4.09          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.88/4.09             (k1_zfmisc_1 @ 
% 3.88/4.09              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 3.88/4.09      inference('simplify', [status(thm)], ['171'])).
% 3.88/4.09  thf('173', plain,
% 3.88/4.09      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 3.88/4.09        | ~ (v1_relat_1 @ sk_C)
% 3.88/4.09        | ~ (v1_funct_1 @ sk_C)
% 3.88/4.09        | ~ (v2_funct_1 @ sk_C))),
% 3.88/4.09      inference('sup+', [status(thm)], ['168', '172'])).
% 3.88/4.09  thf('174', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.88/4.09      inference('sup+', [status(thm)], ['40', '41'])).
% 3.88/4.09  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 3.88/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.88/4.09  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 3.88/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.09  thf('178', plain,
% 3.88/4.09      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.88/4.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.88/4.09      inference('demod', [status(thm)], ['173', '174', '175', '176', '177'])).
% 3.88/4.09  thf('179', plain, ($false), inference('demod', [status(thm)], ['113', '178'])).
% 3.88/4.09  
% 3.88/4.09  % SZS output end Refutation
% 3.88/4.09  
% 3.88/4.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
