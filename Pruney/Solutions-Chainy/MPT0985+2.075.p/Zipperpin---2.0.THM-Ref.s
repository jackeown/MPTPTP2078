%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHUqOkK5tS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:36 EST 2020

% Result     : Theorem 6.28s
% Output     : Refutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  258 (4219 expanded)
%              Number of leaves         :   42 (1289 expanded)
%              Depth                    :   47
%              Number of atoms          : 1937 (61689 expanded)
%              Number of equality atoms :  108 (2538 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('36',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X37: $i] :
      ( ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('91',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('93',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('94',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('96',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('103',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['102','103'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('105',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','104','105'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('109',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','109'])).

thf('111',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','91','106','107','108'])).

thf('114',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('115',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('117',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('119',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','104','105'])).

thf('126',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('127',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('128',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','128'])).

thf('130',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['102','103'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','104','105'])).

thf('133',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('135',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('139',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','139'])).

thf('141',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','140'])).

thf('142',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['102','103'])).

thf('143',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('144',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('146',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('154',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('156',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['152','158'])).

thf('160',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['110','144','159'])).

thf('161',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','160','161'])).

thf('163',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','162'])).

thf('164',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['32','33'])).

thf('166',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('167',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('168',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('169',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['166','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','179'])).

thf('181',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('183',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('184',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('189',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','162'])).

thf('194',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['187','194'])).

thf('196',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['182','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['181','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('207',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('209',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','209','210','211','212'])).

thf('214',plain,(
    $false ),
    inference(demod,[status(thm)],['163','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHUqOkK5tS
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.28/6.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.28/6.48  % Solved by: fo/fo7.sh
% 6.28/6.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.28/6.48  % done 5712 iterations in 6.027s
% 6.28/6.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.28/6.48  % SZS output start Refutation
% 6.28/6.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.28/6.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.28/6.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.28/6.48  thf(sk_A_type, type, sk_A: $i).
% 6.28/6.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.28/6.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.28/6.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.28/6.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.28/6.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.28/6.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.28/6.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.28/6.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.28/6.48  thf(sk_B_type, type, sk_B: $i).
% 6.28/6.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.28/6.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.28/6.48  thf(sk_C_type, type, sk_C: $i).
% 6.28/6.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.28/6.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.28/6.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.28/6.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.28/6.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.28/6.48  thf(t31_funct_2, conjecture,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.28/6.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.28/6.48       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.28/6.48         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.28/6.48           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.28/6.48           ( m1_subset_1 @
% 6.28/6.48             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.28/6.48  thf(zf_stmt_0, negated_conjecture,
% 6.28/6.48    (~( ![A:$i,B:$i,C:$i]:
% 6.28/6.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.28/6.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.28/6.48          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.28/6.48            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.28/6.48              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.28/6.48              ( m1_subset_1 @
% 6.28/6.48                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 6.28/6.48    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 6.28/6.48  thf('0', plain,
% 6.28/6.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 6.28/6.48        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('1', plain,
% 6.28/6.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 6.28/6.48         <= (~
% 6.28/6.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('2', plain,
% 6.28/6.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf(cc1_relset_1, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( v1_relat_1 @ C ) ))).
% 6.28/6.48  thf('3', plain,
% 6.28/6.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.28/6.48         ((v1_relat_1 @ X17)
% 6.28/6.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.28/6.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.28/6.48  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf(dt_k2_funct_1, axiom,
% 6.28/6.48    (![A:$i]:
% 6.28/6.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.28/6.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.28/6.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.28/6.48  thf('5', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('6', plain,
% 6.28/6.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.28/6.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('7', plain,
% 6.28/6.48      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 6.28/6.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['5', '6'])).
% 6.28/6.48  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('9', plain,
% 6.28/6.48      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('demod', [status(thm)], ['7', '8'])).
% 6.28/6.48  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['4', '9'])).
% 6.28/6.48  thf('11', plain,
% 6.28/6.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf(d1_funct_2, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.28/6.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.28/6.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.28/6.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.28/6.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.28/6.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.28/6.48  thf(zf_stmt_1, axiom,
% 6.28/6.48    (![B:$i,A:$i]:
% 6.28/6.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.28/6.48       ( zip_tseitin_0 @ B @ A ) ))).
% 6.28/6.48  thf('12', plain,
% 6.28/6.48      (![X29 : $i, X30 : $i]:
% 6.28/6.48         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.28/6.48  thf('13', plain,
% 6.28/6.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.28/6.48  thf(zf_stmt_3, axiom,
% 6.28/6.48    (![C:$i,B:$i,A:$i]:
% 6.28/6.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.28/6.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.28/6.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.28/6.48  thf(zf_stmt_5, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.28/6.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.28/6.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.28/6.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.28/6.48  thf('14', plain,
% 6.28/6.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.28/6.48         (~ (zip_tseitin_0 @ X34 @ X35)
% 6.28/6.48          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 6.28/6.48          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.28/6.48  thf('15', plain,
% 6.28/6.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['13', '14'])).
% 6.28/6.48  thf('16', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['12', '15'])).
% 6.28/6.48  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('18', plain,
% 6.28/6.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.28/6.48         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 6.28/6.48          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 6.28/6.48          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.28/6.48  thf('19', plain,
% 6.28/6.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 6.28/6.48        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['17', '18'])).
% 6.28/6.48  thf('20', plain,
% 6.28/6.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf(redefinition_k1_relset_1, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.28/6.48  thf('21', plain,
% 6.28/6.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.28/6.48         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 6.28/6.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.28/6.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.28/6.48  thf('22', plain,
% 6.28/6.48      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.28/6.48      inference('sup-', [status(thm)], ['20', '21'])).
% 6.28/6.48  thf('23', plain,
% 6.28/6.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['19', '22'])).
% 6.28/6.48  thf('24', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['16', '23'])).
% 6.28/6.48  thf(t55_funct_1, axiom,
% 6.28/6.48    (![A:$i]:
% 6.28/6.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.28/6.48       ( ( v2_funct_1 @ A ) =>
% 6.28/6.48         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.28/6.48           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.28/6.48  thf('25', plain,
% 6.28/6.48      (![X16 : $i]:
% 6.28/6.48         (~ (v2_funct_1 @ X16)
% 6.28/6.48          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 6.28/6.48          | ~ (v1_funct_1 @ X16)
% 6.28/6.48          | ~ (v1_relat_1 @ X16))),
% 6.28/6.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.28/6.48  thf('26', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('27', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('28', plain,
% 6.28/6.48      (![X16 : $i]:
% 6.28/6.48         (~ (v2_funct_1 @ X16)
% 6.28/6.48          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 6.28/6.48          | ~ (v1_funct_1 @ X16)
% 6.28/6.48          | ~ (v1_relat_1 @ X16))),
% 6.28/6.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.28/6.48  thf('29', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('30', plain,
% 6.28/6.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf(redefinition_k2_relset_1, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.28/6.48  thf('31', plain,
% 6.28/6.48      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.28/6.48         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 6.28/6.48          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.28/6.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.28/6.48  thf('32', plain,
% 6.28/6.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.28/6.48      inference('sup-', [status(thm)], ['30', '31'])).
% 6.28/6.48  thf('33', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('34', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.28/6.48      inference('sup+', [status(thm)], ['32', '33'])).
% 6.28/6.48  thf('35', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('36', plain,
% 6.28/6.48      (![X16 : $i]:
% 6.28/6.48         (~ (v2_funct_1 @ X16)
% 6.28/6.48          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 6.28/6.48          | ~ (v1_funct_1 @ X16)
% 6.28/6.48          | ~ (v1_relat_1 @ X16))),
% 6.28/6.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.28/6.48  thf(d10_xboole_0, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.28/6.48  thf('37', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.28/6.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.28/6.48  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.28/6.48      inference('simplify', [status(thm)], ['37'])).
% 6.28/6.48  thf(d18_relat_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( v1_relat_1 @ B ) =>
% 6.28/6.48       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 6.28/6.48  thf('39', plain,
% 6.28/6.48      (![X9 : $i, X10 : $i]:
% 6.28/6.48         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 6.28/6.48          | (v4_relat_1 @ X9 @ X10)
% 6.28/6.48          | ~ (v1_relat_1 @ X9))),
% 6.28/6.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 6.28/6.48  thf('40', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['38', '39'])).
% 6.28/6.48  thf('41', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.28/6.48      inference('sup+', [status(thm)], ['36', '40'])).
% 6.28/6.48  thf('42', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['35', '41'])).
% 6.28/6.48  thf('43', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['42'])).
% 6.28/6.48  thf('44', plain,
% 6.28/6.48      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 6.28/6.48        | ~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v2_funct_1 @ sk_C))),
% 6.28/6.48      inference('sup+', [status(thm)], ['34', '43'])).
% 6.28/6.48  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('48', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 6.28/6.48      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 6.28/6.48  thf('49', plain,
% 6.28/6.48      (![X9 : $i, X10 : $i]:
% 6.28/6.48         (~ (v4_relat_1 @ X9 @ X10)
% 6.28/6.48          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 6.28/6.48          | ~ (v1_relat_1 @ X9))),
% 6.28/6.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 6.28/6.48  thf('50', plain,
% 6.28/6.48      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 6.28/6.48      inference('sup-', [status(thm)], ['48', '49'])).
% 6.28/6.48  thf('51', plain,
% 6.28/6.48      ((~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 6.28/6.48      inference('sup-', [status(thm)], ['29', '50'])).
% 6.28/6.48  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 6.28/6.48      inference('demod', [status(thm)], ['51', '52', '53'])).
% 6.28/6.48  thf('55', plain,
% 6.28/6.48      (![X0 : $i, X2 : $i]:
% 6.28/6.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.28/6.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.28/6.48  thf('56', plain,
% 6.28/6.48      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.28/6.48        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['54', '55'])).
% 6.28/6.48  thf('57', plain,
% 6.28/6.48      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 6.28/6.48        | ~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v2_funct_1 @ sk_C)
% 6.28/6.48        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['28', '56'])).
% 6.28/6.48  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.28/6.48      inference('sup+', [status(thm)], ['32', '33'])).
% 6.28/6.48  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.28/6.48      inference('simplify', [status(thm)], ['37'])).
% 6.28/6.48  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('63', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 6.28/6.48  thf(t3_funct_2, axiom,
% 6.28/6.48    (![A:$i]:
% 6.28/6.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.28/6.48       ( ( v1_funct_1 @ A ) & 
% 6.28/6.48         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 6.28/6.48         ( m1_subset_1 @
% 6.28/6.48           A @ 
% 6.28/6.48           ( k1_zfmisc_1 @
% 6.28/6.48             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.28/6.48  thf('64', plain,
% 6.28/6.48      (![X37 : $i]:
% 6.28/6.48         ((v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))
% 6.28/6.48          | ~ (v1_funct_1 @ X37)
% 6.28/6.48          | ~ (v1_relat_1 @ X37))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.28/6.48  thf('65', plain,
% 6.28/6.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 6.28/6.48         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.28/6.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('sup+', [status(thm)], ['63', '64'])).
% 6.28/6.48  thf('66', plain,
% 6.28/6.48      ((~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 6.28/6.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['27', '65'])).
% 6.28/6.48  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('69', plain,
% 6.28/6.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 6.28/6.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.28/6.48  thf('70', plain,
% 6.28/6.48      ((~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 6.28/6.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['26', '69'])).
% 6.28/6.48  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('73', plain,
% 6.28/6.48      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 6.28/6.48        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['70', '71', '72'])).
% 6.28/6.48  thf('74', plain,
% 6.28/6.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 6.28/6.48        | ~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v2_funct_1 @ sk_C))),
% 6.28/6.48      inference('sup+', [status(thm)], ['25', '73'])).
% 6.28/6.48  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('78', plain,
% 6.28/6.48      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 6.28/6.48      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 6.28/6.48  thf('79', plain,
% 6.28/6.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 6.28/6.48        | ((sk_B) = (k1_xboole_0)))),
% 6.28/6.48      inference('sup+', [status(thm)], ['24', '78'])).
% 6.28/6.48  thf('80', plain,
% 6.28/6.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('81', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['79', '80'])).
% 6.28/6.48  thf('82', plain,
% 6.28/6.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['11', '81'])).
% 6.28/6.48  thf('83', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['79', '80'])).
% 6.28/6.48  thf('84', plain,
% 6.28/6.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf(t3_subset, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.28/6.48  thf('85', plain,
% 6.28/6.48      (![X6 : $i, X7 : $i]:
% 6.28/6.48         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.28/6.48  thf('86', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 6.28/6.48      inference('sup-', [status(thm)], ['84', '85'])).
% 6.28/6.48  thf('87', plain,
% 6.28/6.48      (![X0 : $i, X2 : $i]:
% 6.28/6.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.28/6.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.28/6.48  thf('88', plain,
% 6.28/6.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 6.28/6.48        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['86', '87'])).
% 6.28/6.48  thf('89', plain,
% 6.28/6.48      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 6.28/6.48         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['83', '88'])).
% 6.28/6.48  thf(t113_zfmisc_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.28/6.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.28/6.48  thf('90', plain,
% 6.28/6.48      (![X4 : $i, X5 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.28/6.48  thf('91', plain,
% 6.28/6.48      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['90'])).
% 6.28/6.48  thf('92', plain,
% 6.28/6.48      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['90'])).
% 6.28/6.48  thf('93', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.28/6.48      inference('simplify', [status(thm)], ['37'])).
% 6.28/6.48  thf('94', plain,
% 6.28/6.48      (![X6 : $i, X8 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.28/6.48  thf('95', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['93', '94'])).
% 6.28/6.48  thf(cc2_relset_1, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.28/6.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.28/6.48  thf('96', plain,
% 6.28/6.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.28/6.48         ((v4_relat_1 @ X20 @ X21)
% 6.28/6.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.28/6.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.28/6.48  thf('97', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 6.28/6.48      inference('sup-', [status(thm)], ['95', '96'])).
% 6.28/6.48  thf('98', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 6.28/6.48      inference('sup+', [status(thm)], ['92', '97'])).
% 6.28/6.48  thf('99', plain,
% 6.28/6.48      (![X9 : $i, X10 : $i]:
% 6.28/6.48         (~ (v4_relat_1 @ X9 @ X10)
% 6.28/6.48          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 6.28/6.48          | ~ (v1_relat_1 @ X9))),
% 6.28/6.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 6.28/6.48  thf('100', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ k1_xboole_0)
% 6.28/6.48          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['98', '99'])).
% 6.28/6.48  thf('101', plain,
% 6.28/6.48      (![X4 : $i, X5 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.28/6.48  thf('102', plain,
% 6.28/6.48      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['101'])).
% 6.28/6.48  thf(fc6_relat_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.28/6.48  thf('103', plain,
% 6.28/6.48      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 6.28/6.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.28/6.48  thf('104', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.28/6.48      inference('sup+', [status(thm)], ['102', '103'])).
% 6.28/6.48  thf(t60_relat_1, axiom,
% 6.28/6.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.28/6.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.28/6.48  thf('105', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.28/6.48  thf('106', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.28/6.48      inference('demod', [status(thm)], ['100', '104', '105'])).
% 6.28/6.48  thf('107', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['79', '80'])).
% 6.28/6.48  thf('108', plain,
% 6.28/6.48      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['90'])).
% 6.28/6.48  thf('109', plain,
% 6.28/6.48      ((((k1_xboole_0) = (sk_C)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['89', '91', '106', '107', '108'])).
% 6.28/6.48  thf('110', plain,
% 6.28/6.48      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['82', '109'])).
% 6.28/6.48  thf('111', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('112', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('113', plain,
% 6.28/6.48      ((((k1_xboole_0) = (sk_C)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['89', '91', '106', '107', '108'])).
% 6.28/6.48  thf('114', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 6.28/6.48  thf('115', plain,
% 6.28/6.48      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup+', [status(thm)], ['113', '114'])).
% 6.28/6.48  thf('116', plain,
% 6.28/6.48      ((((sk_B) = (k1_xboole_0)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['79', '80'])).
% 6.28/6.48  thf('117', plain,
% 6.28/6.48      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['115', '116'])).
% 6.28/6.48  thf('118', plain,
% 6.28/6.48      (![X37 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X37 @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 6.28/6.48          | ~ (v1_funct_1 @ X37)
% 6.28/6.48          | ~ (v1_relat_1 @ X37))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.28/6.48  thf('119', plain,
% 6.28/6.48      (![X6 : $i, X7 : $i]:
% 6.28/6.48         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.28/6.48  thf('120', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | (r1_tarski @ X0 @ 
% 6.28/6.48             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['118', '119'])).
% 6.28/6.48  thf('121', plain,
% 6.28/6.48      (![X0 : $i, X2 : $i]:
% 6.28/6.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.28/6.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.28/6.48  thf('122', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (r1_tarski @ 
% 6.28/6.48               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 6.28/6.48          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['120', '121'])).
% 6.28/6.48  thf('123', plain,
% 6.28/6.48      (((~ (r1_tarski @ 
% 6.28/6.48            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 6.28/6.48             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))) @ 
% 6.28/6.48            (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 6.28/6.48             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 6.28/6.48             = (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['117', '122'])).
% 6.28/6.48  thf('124', plain,
% 6.28/6.48      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['101'])).
% 6.28/6.48  thf('125', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.28/6.48      inference('demod', [status(thm)], ['100', '104', '105'])).
% 6.28/6.48  thf('126', plain,
% 6.28/6.48      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['115', '116'])).
% 6.28/6.48  thf('127', plain,
% 6.28/6.48      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['101'])).
% 6.28/6.48  thf('128', plain,
% 6.28/6.48      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 6.28/6.48  thf('129', plain,
% 6.28/6.48      (((~ (v1_relat_1 @ k1_xboole_0)
% 6.28/6.48         | ~ (v1_funct_1 @ k1_xboole_0)
% 6.28/6.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['112', '128'])).
% 6.28/6.48  thf('130', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.28/6.48      inference('sup+', [status(thm)], ['102', '103'])).
% 6.28/6.48  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('132', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.28/6.48      inference('demod', [status(thm)], ['100', '104', '105'])).
% 6.28/6.48  thf('133', plain,
% 6.28/6.48      (![X6 : $i, X8 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.28/6.48  thf('134', plain,
% 6.28/6.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['132', '133'])).
% 6.28/6.48  thf(cc3_funct_1, axiom,
% 6.28/6.48    (![A:$i]:
% 6.28/6.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.28/6.48       ( ![B:$i]:
% 6.28/6.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 6.28/6.48  thf('135', plain,
% 6.28/6.48      (![X13 : $i, X14 : $i]:
% 6.28/6.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 6.28/6.48          | (v1_funct_1 @ X13)
% 6.28/6.48          | ~ (v1_funct_1 @ X14)
% 6.28/6.48          | ~ (v1_relat_1 @ X14))),
% 6.28/6.48      inference('cnf', [status(esa)], [cc3_funct_1])).
% 6.28/6.48  thf('136', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | (v1_funct_1 @ k1_xboole_0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['134', '135'])).
% 6.28/6.48  thf('137', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C))),
% 6.28/6.48      inference('sup-', [status(thm)], ['131', '136'])).
% 6.28/6.48  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('139', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.28/6.48      inference('demod', [status(thm)], ['137', '138'])).
% 6.28/6.48  thf('140', plain,
% 6.28/6.48      (((~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 6.28/6.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['129', '130', '139'])).
% 6.28/6.48  thf('141', plain,
% 6.28/6.48      (((~ (v1_relat_1 @ k1_xboole_0)
% 6.28/6.48         | ~ (v1_funct_1 @ k1_xboole_0)
% 6.28/6.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['111', '140'])).
% 6.28/6.48  thf('142', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.28/6.48      inference('sup+', [status(thm)], ['102', '103'])).
% 6.28/6.48  thf('143', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.28/6.48      inference('demod', [status(thm)], ['137', '138'])).
% 6.28/6.48  thf('144', plain,
% 6.28/6.48      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 6.28/6.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['141', '142', '143'])).
% 6.28/6.48  thf('145', plain,
% 6.28/6.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['132', '133'])).
% 6.28/6.48  thf('146', plain,
% 6.28/6.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.28/6.48         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 6.28/6.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.28/6.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.28/6.48  thf('147', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['145', '146'])).
% 6.28/6.48  thf('148', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.28/6.48  thf('149', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('demod', [status(thm)], ['147', '148'])).
% 6.28/6.48  thf('150', plain,
% 6.28/6.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.28/6.48         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 6.28/6.48          | (v1_funct_2 @ X33 @ X31 @ X32)
% 6.28/6.48          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.28/6.48  thf('151', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (((X1) != (k1_xboole_0))
% 6.28/6.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 6.28/6.48          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['149', '150'])).
% 6.28/6.48  thf('152', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 6.28/6.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['151'])).
% 6.28/6.48  thf('153', plain,
% 6.28/6.48      (![X29 : $i, X30 : $i]:
% 6.28/6.48         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.28/6.48  thf('154', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 6.28/6.48      inference('simplify', [status(thm)], ['153'])).
% 6.28/6.48  thf('155', plain,
% 6.28/6.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['132', '133'])).
% 6.28/6.48  thf('156', plain,
% 6.28/6.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.28/6.48         (~ (zip_tseitin_0 @ X34 @ X35)
% 6.28/6.48          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 6.28/6.48          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.28/6.48  thf('157', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 6.28/6.48      inference('sup-', [status(thm)], ['155', '156'])).
% 6.28/6.48  thf('158', plain,
% 6.28/6.48      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.28/6.48      inference('sup-', [status(thm)], ['154', '157'])).
% 6.28/6.48  thf('159', plain,
% 6.28/6.48      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.28/6.48      inference('demod', [status(thm)], ['152', '158'])).
% 6.28/6.48  thf('160', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 6.28/6.48      inference('demod', [status(thm)], ['110', '144', '159'])).
% 6.28/6.48  thf('161', plain,
% 6.28/6.48      (~
% 6.28/6.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 6.28/6.48       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 6.28/6.48       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('162', plain,
% 6.28/6.48      (~
% 6.28/6.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.28/6.48      inference('sat_resolution*', [status(thm)], ['10', '160', '161'])).
% 6.28/6.48  thf('163', plain,
% 6.28/6.48      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.28/6.48      inference('simpl_trail', [status(thm)], ['1', '162'])).
% 6.28/6.48  thf('164', plain,
% 6.28/6.48      (![X16 : $i]:
% 6.28/6.48         (~ (v2_funct_1 @ X16)
% 6.28/6.48          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 6.28/6.48          | ~ (v1_funct_1 @ X16)
% 6.28/6.48          | ~ (v1_relat_1 @ X16))),
% 6.28/6.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.28/6.48  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.28/6.48      inference('sup+', [status(thm)], ['32', '33'])).
% 6.28/6.48  thf('166', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('167', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('168', plain,
% 6.28/6.48      (![X16 : $i]:
% 6.28/6.48         (~ (v2_funct_1 @ X16)
% 6.28/6.48          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 6.28/6.48          | ~ (v1_funct_1 @ X16)
% 6.28/6.48          | ~ (v1_relat_1 @ X16))),
% 6.28/6.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.28/6.48  thf('169', plain,
% 6.28/6.48      (![X37 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X37 @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 6.28/6.48          | ~ (v1_funct_1 @ X37)
% 6.28/6.48          | ~ (v1_relat_1 @ X37))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.28/6.48  thf('170', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.28/6.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.28/6.48      inference('sup+', [status(thm)], ['168', '169'])).
% 6.28/6.48  thf('171', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.28/6.48             (k1_zfmisc_1 @ 
% 6.28/6.48              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 6.28/6.48               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['167', '170'])).
% 6.28/6.48  thf('172', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['171'])).
% 6.28/6.48  thf('173', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.28/6.48             (k1_zfmisc_1 @ 
% 6.28/6.48              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 6.28/6.48               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.28/6.48      inference('sup-', [status(thm)], ['166', '172'])).
% 6.28/6.48  thf('174', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.28/6.48          | ~ (v2_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['173'])).
% 6.28/6.48  thf('175', plain,
% 6.28/6.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48         (k1_zfmisc_1 @ 
% 6.28/6.48          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 6.28/6.48        | ~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v2_funct_1 @ sk_C))),
% 6.28/6.48      inference('sup+', [status(thm)], ['165', '174'])).
% 6.28/6.48  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('179', plain,
% 6.28/6.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48        (k1_zfmisc_1 @ 
% 6.28/6.48         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 6.28/6.48      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 6.28/6.48  thf('180', plain,
% 6.28/6.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 6.28/6.48        | ~ (v1_relat_1 @ sk_C)
% 6.28/6.48        | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48        | ~ (v2_funct_1 @ sk_C))),
% 6.28/6.48      inference('sup+', [status(thm)], ['164', '179'])).
% 6.28/6.48  thf('181', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('182', plain,
% 6.28/6.48      (![X15 : $i]:
% 6.28/6.48         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 6.28/6.48          | ~ (v1_funct_1 @ X15)
% 6.28/6.48          | ~ (v1_relat_1 @ X15))),
% 6.28/6.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.28/6.48  thf('183', plain,
% 6.28/6.48      (![X29 : $i, X30 : $i]:
% 6.28/6.48         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.28/6.48  thf('184', plain,
% 6.28/6.48      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['101'])).
% 6.28/6.48  thf('185', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.28/6.48      inference('sup+', [status(thm)], ['183', '184'])).
% 6.28/6.48  thf('186', plain,
% 6.28/6.48      (![X37 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X37 @ 
% 6.28/6.48           (k1_zfmisc_1 @ 
% 6.28/6.48            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 6.28/6.48          | ~ (v1_funct_1 @ X37)
% 6.28/6.48          | ~ (v1_relat_1 @ X37))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.28/6.48  thf('187', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.28/6.48          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 6.28/6.48          | ~ (v1_relat_1 @ X0)
% 6.28/6.48          | ~ (v1_funct_1 @ X0))),
% 6.28/6.48      inference('sup+', [status(thm)], ['185', '186'])).
% 6.28/6.48  thf('188', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.28/6.48      inference('sup+', [status(thm)], ['183', '184'])).
% 6.28/6.48  thf('189', plain,
% 6.28/6.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['13', '14'])).
% 6.28/6.48  thf('190', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 6.28/6.48          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['188', '189'])).
% 6.28/6.48  thf('191', plain,
% 6.28/6.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['19', '22'])).
% 6.28/6.48  thf('192', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 6.28/6.48          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['190', '191'])).
% 6.28/6.48  thf('193', plain,
% 6.28/6.48      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.28/6.48      inference('simpl_trail', [status(thm)], ['1', '162'])).
% 6.28/6.48  thf('194', plain,
% 6.28/6.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.28/6.48        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['192', '193'])).
% 6.28/6.48  thf('195', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48          | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 6.28/6.48          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['187', '194'])).
% 6.28/6.48  thf('196', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 6.28/6.48  thf('197', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.28/6.48          | (zip_tseitin_0 @ sk_B @ X0)
% 6.28/6.48          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['195', '196'])).
% 6.28/6.48  thf('198', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ sk_C)
% 6.28/6.48          | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48          | ((sk_A) = (k1_relat_1 @ sk_C))
% 6.28/6.48          | (zip_tseitin_0 @ sk_B @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['182', '197'])).
% 6.28/6.48  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('201', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (((sk_A) = (k1_relat_1 @ sk_C))
% 6.28/6.48          | (zip_tseitin_0 @ sk_B @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['198', '199', '200'])).
% 6.28/6.48  thf('202', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ sk_C)
% 6.28/6.48          | ~ (v1_funct_1 @ sk_C)
% 6.28/6.48          | (zip_tseitin_0 @ sk_B @ X0)
% 6.28/6.48          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['181', '201'])).
% 6.28/6.48  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('205', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['202', '203', '204'])).
% 6.28/6.48  thf('206', plain,
% 6.28/6.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['13', '14'])).
% 6.28/6.48  thf('207', plain,
% 6.28/6.48      ((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 6.28/6.48      inference('sup-', [status(thm)], ['205', '206'])).
% 6.28/6.48  thf('208', plain,
% 6.28/6.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.28/6.48      inference('demod', [status(thm)], ['19', '22'])).
% 6.28/6.48  thf('209', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 6.28/6.48      inference('clc', [status(thm)], ['207', '208'])).
% 6.28/6.48  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 6.28/6.48      inference('sup-', [status(thm)], ['2', '3'])).
% 6.28/6.48  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('213', plain,
% 6.28/6.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.28/6.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['180', '209', '210', '211', '212'])).
% 6.28/6.48  thf('214', plain, ($false), inference('demod', [status(thm)], ['163', '213'])).
% 6.28/6.48  
% 6.28/6.48  % SZS output end Refutation
% 6.28/6.48  
% 6.28/6.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
