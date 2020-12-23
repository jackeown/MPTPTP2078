%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3bEkF4Uio

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 4.75s
% Output     : Refutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  278 (12675 expanded)
%              Number of leaves         :   41 (3686 expanded)
%              Depth                    :   41
%              Number of atoms          : 2276 (189495 expanded)
%              Number of equality atoms :  141 (8755 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X38: $i] :
      ( ( v1_funct_2 @ X38 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['55','60','61','62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','66'])).

thf('68',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('76',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('82',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','79','82','85','88'])).

thf('90',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','66'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','91','92'])).

thf('94',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('98',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('99',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('101',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['97','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('113',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['112','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','121'])).

thf('123',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['96','122'])).

thf('124',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('125',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('127',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relset_1 @ X0 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('133',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('134',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('139',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','140'])).

thf('142',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('143',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','141','142'])).

thf('144',plain,(
    ! [X38: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('145',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('152',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','141','142'])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('154',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151','152','153'])).

thf('155',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','154'])).

thf('156',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('157',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('158',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('160',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('161',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','158','161'])).

thf('163',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','162'])).

thf('164',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['156','157'])).

thf('165',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('166',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('168',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','140'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('174',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('176',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['172','178'])).

thf('180',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['93','166','179'])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('182',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','180','181'])).

thf('183',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','182'])).

thf('184',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('185',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('186',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('187',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','121'])).

thf('188',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('189',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('191',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('193',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('194',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('195',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('196',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['194','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['193','201'])).

thf('203',plain,(
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
    inference('sup-',[status(thm)],['192','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['191','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['190','206'])).

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
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['207','208','209','210'])).

thf('212',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','182'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['189','215'])).

thf('217',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','216'])).

thf('218',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','217'])).

thf('219',plain,(
    ! [X38: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('220',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['186','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['185','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','228'])).

thf('230',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233'])).

thf('235',plain,(
    $false ),
    inference(demod,[status(thm)],['183','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3bEkF4Uio
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:27:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.75/4.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.75/4.99  % Solved by: fo/fo7.sh
% 4.75/4.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.75/4.99  % done 3505 iterations in 4.532s
% 4.75/4.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.75/4.99  % SZS output start Refutation
% 4.75/4.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.75/4.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.75/4.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.75/4.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.75/4.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.75/4.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.75/4.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.75/4.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.75/4.99  thf(sk_B_type, type, sk_B: $i).
% 4.75/4.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.75/4.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.75/4.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.75/4.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.75/4.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.75/4.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.75/4.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.75/4.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.75/4.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.75/4.99  thf(sk_C_type, type, sk_C: $i).
% 4.75/4.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.75/4.99  thf(sk_A_type, type, sk_A: $i).
% 4.75/4.99  thf(t31_funct_2, conjecture,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.75/4.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.75/4.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.75/4.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.75/4.99           ( m1_subset_1 @
% 4.75/4.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.75/4.99  thf(zf_stmt_0, negated_conjecture,
% 4.75/4.99    (~( ![A:$i,B:$i,C:$i]:
% 4.75/4.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.75/4.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.99          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.75/4.99            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.75/4.99              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.75/4.99              ( m1_subset_1 @
% 4.75/4.99                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 4.75/4.99    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 4.75/4.99  thf('0', plain,
% 4.75/4.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.75/4.99        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 4.75/4.99        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('1', plain,
% 4.75/4.99      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.75/4.99         <= (~
% 4.75/4.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.75/4.99      inference('split', [status(esa)], ['0'])).
% 4.75/4.99  thf('2', plain,
% 4.75/4.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf(cc1_relset_1, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( v1_relat_1 @ C ) ))).
% 4.75/4.99  thf('3', plain,
% 4.75/4.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.75/4.99         ((v1_relat_1 @ X18)
% 4.75/4.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.75/4.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.75/4.99  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf(dt_k2_funct_1, axiom,
% 4.75/4.99    (![A:$i]:
% 4.75/4.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.75/4.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.75/4.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.75/4.99  thf('5', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('6', plain,
% 4.75/4.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.75/4.99      inference('split', [status(esa)], ['0'])).
% 4.75/4.99  thf('7', plain,
% 4.75/4.99      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['5', '6'])).
% 4.75/4.99  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('9', plain,
% 4.75/4.99      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.75/4.99      inference('demod', [status(thm)], ['7', '8'])).
% 4.75/4.99  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['4', '9'])).
% 4.75/4.99  thf('11', plain,
% 4.75/4.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('split', [status(esa)], ['0'])).
% 4.75/4.99  thf(d1_funct_2, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.75/4.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.75/4.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.75/4.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.75/4.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.75/4.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.75/4.99  thf(zf_stmt_1, axiom,
% 4.75/4.99    (![B:$i,A:$i]:
% 4.75/4.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.75/4.99       ( zip_tseitin_0 @ B @ A ) ))).
% 4.75/4.99  thf('12', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf('13', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf(t113_zfmisc_1, axiom,
% 4.75/4.99    (![A:$i,B:$i]:
% 4.75/4.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.75/4.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.75/4.99  thf('14', plain,
% 4.75/4.99      (![X4 : $i, X5 : $i]:
% 4.75/4.99         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.75/4.99  thf('15', plain,
% 4.75/4.99      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['14'])).
% 4.75/4.99  thf('16', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.99         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.75/4.99      inference('sup+', [status(thm)], ['13', '15'])).
% 4.75/4.99  thf('17', plain,
% 4.75/4.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('18', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.75/4.99          | (zip_tseitin_0 @ sk_B @ X0))),
% 4.75/4.99      inference('sup+', [status(thm)], ['16', '17'])).
% 4.75/4.99  thf('19', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.99         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 4.75/4.99          | (zip_tseitin_0 @ X0 @ X2)
% 4.75/4.99          | (zip_tseitin_0 @ sk_B @ X1))),
% 4.75/4.99      inference('sup+', [status(thm)], ['12', '18'])).
% 4.75/4.99  thf('20', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ sk_B @ X0)
% 4.75/4.99          | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))),
% 4.75/4.99      inference('eq_fact', [status(thm)], ['19'])).
% 4.75/4.99  thf(t3_subset, axiom,
% 4.75/4.99    (![A:$i,B:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.75/4.99  thf('21', plain,
% 4.75/4.99      (![X7 : $i, X8 : $i]:
% 4.75/4.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.75/4.99  thf('22', plain,
% 4.75/4.99      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 4.75/4.99      inference('sup-', [status(thm)], ['20', '21'])).
% 4.75/4.99  thf(d10_xboole_0, axiom,
% 4.75/4.99    (![A:$i,B:$i]:
% 4.75/4.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.75/4.99  thf('23', plain,
% 4.75/4.99      (![X0 : $i, X2 : $i]:
% 4.75/4.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.75/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.99  thf('24', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ sk_B @ X0)
% 4.75/4.99          | ~ (r1_tarski @ sk_B @ sk_C)
% 4.75/4.99          | ((sk_B) = (sk_C)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['22', '23'])).
% 4.75/4.99  thf('25', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf(t4_subset_1, axiom,
% 4.75/4.99    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.75/4.99  thf('26', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('27', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.99         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.75/4.99      inference('sup+', [status(thm)], ['25', '26'])).
% 4.75/4.99  thf('28', plain,
% 4.75/4.99      (![X7 : $i, X8 : $i]:
% 4.75/4.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.75/4.99  thf('29', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['27', '28'])).
% 4.75/4.99  thf('30', plain,
% 4.75/4.99      (![X0 : $i]: (((sk_B) = (sk_C)) | (zip_tseitin_0 @ sk_B @ X0))),
% 4.75/4.99      inference('clc', [status(thm)], ['24', '29'])).
% 4.75/4.99  thf('31', plain,
% 4.75/4.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.75/4.99  thf(zf_stmt_3, axiom,
% 4.75/4.99    (![C:$i,B:$i,A:$i]:
% 4.75/4.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.75/4.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.75/4.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.75/4.99  thf(zf_stmt_5, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.75/4.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.75/4.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.75/4.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.75/4.99  thf('32', plain,
% 4.75/4.99      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.75/4.99         (~ (zip_tseitin_0 @ X35 @ X36)
% 4.75/4.99          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 4.75/4.99          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.75/4.99  thf('33', plain,
% 4.75/4.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.75/4.99      inference('sup-', [status(thm)], ['31', '32'])).
% 4.75/4.99  thf('34', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.75/4.99      inference('sup-', [status(thm)], ['30', '33'])).
% 4.75/4.99  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('36', plain,
% 4.75/4.99      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.75/4.99         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 4.75/4.99          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 4.75/4.99          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.75/4.99  thf('37', plain,
% 4.75/4.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 4.75/4.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['35', '36'])).
% 4.75/4.99  thf('38', plain,
% 4.75/4.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf(redefinition_k1_relset_1, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.75/4.99  thf('39', plain,
% 4.75/4.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.75/4.99         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 4.75/4.99          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.75/4.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.75/4.99  thf('40', plain,
% 4.75/4.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 4.75/4.99      inference('sup-', [status(thm)], ['38', '39'])).
% 4.75/4.99  thf('41', plain,
% 4.75/4.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['37', '40'])).
% 4.75/4.99  thf('42', plain, ((((sk_B) = (sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['34', '41'])).
% 4.75/4.99  thf(t55_funct_1, axiom,
% 4.75/4.99    (![A:$i]:
% 4.75/4.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.75/4.99       ( ( v2_funct_1 @ A ) =>
% 4.75/4.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.75/4.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.75/4.99  thf('43', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf('44', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('45', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('46', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf(t3_funct_2, axiom,
% 4.75/4.99    (![A:$i]:
% 4.75/4.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.75/4.99       ( ( v1_funct_1 @ A ) & 
% 4.75/4.99         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 4.75/4.99         ( m1_subset_1 @
% 4.75/4.99           A @ 
% 4.75/4.99           ( k1_zfmisc_1 @
% 4.75/4.99             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.75/4.99  thf('47', plain,
% 4.75/4.99      (![X38 : $i]:
% 4.75/4.99         ((v1_funct_2 @ X38 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))
% 4.75/4.99          | ~ (v1_funct_1 @ X38)
% 4.75/4.99          | ~ (v1_relat_1 @ X38))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.75/4.99  thf('48', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['46', '47'])).
% 4.75/4.99  thf('49', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['45', '48'])).
% 4.75/4.99  thf('50', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['49'])).
% 4.75/4.99  thf('51', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['44', '50'])).
% 4.75/4.99  thf('52', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['51'])).
% 4.75/4.99  thf('53', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99           (k1_relat_1 @ X0))
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0))),
% 4.75/4.99      inference('sup+', [status(thm)], ['43', '52'])).
% 4.75/4.99  thf('54', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99             (k1_relat_1 @ X0)))),
% 4.75/4.99      inference('simplify', [status(thm)], ['53'])).
% 4.75/4.99  thf('55', plain,
% 4.75/4.99      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 4.75/4.99        | ((sk_B) = (sk_C))
% 4.75/4.99        | ~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | ~ (v2_funct_1 @ sk_C))),
% 4.75/4.99      inference('sup+', [status(thm)], ['42', '54'])).
% 4.75/4.99  thf('56', plain,
% 4.75/4.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf(redefinition_k2_relset_1, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.75/4.99  thf('57', plain,
% 4.75/4.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.75/4.99         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 4.75/4.99          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.75/4.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.75/4.99  thf('58', plain,
% 4.75/4.99      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.75/4.99      inference('sup-', [status(thm)], ['56', '57'])).
% 4.75/4.99  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('64', plain,
% 4.75/4.99      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['55', '60', '61', '62', '63'])).
% 4.75/4.99  thf('65', plain,
% 4.75/4.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('split', [status(esa)], ['0'])).
% 4.75/4.99  thf('66', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('67', plain,
% 4.75/4.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['11', '66'])).
% 4.75/4.99  thf('68', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('69', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf('70', plain,
% 4.75/4.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.75/4.99      inference('sup-', [status(thm)], ['31', '32'])).
% 4.75/4.99  thf('71', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.75/4.99      inference('sup-', [status(thm)], ['69', '70'])).
% 4.75/4.99  thf('72', plain,
% 4.75/4.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['37', '40'])).
% 4.75/4.99  thf('73', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['71', '72'])).
% 4.75/4.99  thf('74', plain,
% 4.75/4.99      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['68', '73'])).
% 4.75/4.99  thf('75', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.75/4.99             (k1_relat_1 @ X0)))),
% 4.75/4.99      inference('simplify', [status(thm)], ['53'])).
% 4.75/4.99  thf('76', plain,
% 4.75/4.99      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 4.75/4.99         | ((sk_B) = (k1_xboole_0))
% 4.75/4.99         | ~ (v1_relat_1 @ sk_B)
% 4.75/4.99         | ~ (v1_funct_1 @ sk_B)
% 4.75/4.99         | ~ (v2_funct_1 @ sk_B)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['74', '75'])).
% 4.75/4.99  thf('77', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('78', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('79', plain,
% 4.75/4.99      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['77', '78'])).
% 4.75/4.99  thf('80', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('82', plain,
% 4.75/4.99      (((v1_relat_1 @ sk_B))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['80', '81'])).
% 4.75/4.99  thf('83', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('85', plain,
% 4.75/4.99      (((v1_funct_1 @ sk_B))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['83', '84'])).
% 4.75/4.99  thf('86', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('88', plain,
% 4.75/4.99      (((v2_funct_1 @ sk_B))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['86', '87'])).
% 4.75/4.99  thf('89', plain,
% 4.75/4.99      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 4.75/4.99         | ((sk_B) = (k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['76', '79', '82', '85', '88'])).
% 4.75/4.99  thf('90', plain,
% 4.75/4.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['11', '66'])).
% 4.75/4.99  thf('91', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('clc', [status(thm)], ['89', '90'])).
% 4.75/4.99  thf('92', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('clc', [status(thm)], ['89', '90'])).
% 4.75/4.99  thf('93', plain,
% 4.75/4.99      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['67', '91', '92'])).
% 4.75/4.99  thf('94', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('95', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('96', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('98', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf('99', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf(t155_funct_1, axiom,
% 4.75/4.99    (![A:$i,B:$i]:
% 4.75/4.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.75/4.99       ( ( v2_funct_1 @ B ) =>
% 4.75/4.99         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 4.75/4.99  thf('100', plain,
% 4.75/4.99      (![X15 : $i, X16 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X15)
% 4.75/4.99          | ((k10_relat_1 @ X15 @ X16)
% 4.75/4.99              = (k9_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 4.75/4.99          | ~ (v1_funct_1 @ X15)
% 4.75/4.99          | ~ (v1_relat_1 @ X15))),
% 4.75/4.99      inference('cnf', [status(esa)], [t155_funct_1])).
% 4.75/4.99  thf(t146_relat_1, axiom,
% 4.75/4.99    (![A:$i]:
% 4.75/4.99     ( ( v1_relat_1 @ A ) =>
% 4.75/4.99       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 4.75/4.99  thf('101', plain,
% 4.75/4.99      (![X13 : $i]:
% 4.75/4.99         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 4.75/4.99          | ~ (v1_relat_1 @ X13))),
% 4.75/4.99      inference('cnf', [status(esa)], [t146_relat_1])).
% 4.75/4.99  thf('102', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['100', '101'])).
% 4.75/4.99  thf('103', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['99', '102'])).
% 4.75/4.99  thf('104', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['103'])).
% 4.75/4.99  thf('105', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 4.75/4.99            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0))),
% 4.75/4.99      inference('sup+', [status(thm)], ['98', '104'])).
% 4.75/4.99  thf('106', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 4.75/4.99              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.75/4.99      inference('simplify', [status(thm)], ['105'])).
% 4.75/4.99  thf('107', plain,
% 4.75/4.99      ((((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.75/4.99        | ~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | ~ (v2_funct_1 @ sk_C))),
% 4.75/4.99      inference('sup+', [status(thm)], ['97', '106'])).
% 4.75/4.99  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('111', plain,
% 4.75/4.99      (((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 4.75/4.99  thf('112', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('113', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf('114', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 4.75/4.99              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.75/4.99      inference('simplify', [status(thm)], ['105'])).
% 4.75/4.99  thf('115', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0))),
% 4.75/4.99      inference('sup+', [status(thm)], ['113', '114'])).
% 4.75/4.99  thf('116', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 4.75/4.99      inference('simplify', [status(thm)], ['115'])).
% 4.75/4.99  thf('117', plain,
% 4.75/4.99      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 4.75/4.99        | ~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | ~ (v2_funct_1 @ sk_C))),
% 4.75/4.99      inference('sup+', [status(thm)], ['112', '116'])).
% 4.75/4.99  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('121', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 4.75/4.99      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 4.75/4.99  thf('122', plain,
% 4.75/4.99      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['111', '121'])).
% 4.75/4.99  thf('123', plain,
% 4.75/4.99      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['96', '122'])).
% 4.75/4.99  thf('124', plain,
% 4.75/4.99      ((((sk_B) = (sk_C)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.99  thf('125', plain,
% 4.75/4.99      ((((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['123', '124'])).
% 4.75/4.99  thf('126', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('clc', [status(thm)], ['89', '90'])).
% 4.75/4.99  thf('127', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf(dt_k1_relset_1, axiom,
% 4.75/4.99    (![A:$i,B:$i,C:$i]:
% 4.75/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.99       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.75/4.99  thf('128', plain,
% 4.75/4.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.75/4.99         ((m1_subset_1 @ (k1_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X21))
% 4.75/4.99          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 4.75/4.99  thf('129', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 4.75/4.99          (k1_zfmisc_1 @ X1))),
% 4.75/4.99      inference('sup-', [status(thm)], ['127', '128'])).
% 4.75/4.99  thf('130', plain,
% 4.75/4.99      (![X7 : $i, X8 : $i]:
% 4.75/4.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.75/4.99  thf('131', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (r1_tarski @ (k1_relset_1 @ X0 @ X1 @ k1_xboole_0) @ X0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['129', '130'])).
% 4.75/4.99  thf('132', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('133', plain,
% 4.75/4.99      (![X7 : $i, X8 : $i]:
% 4.75/4.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.75/4.99  thf('134', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['132', '133'])).
% 4.75/4.99  thf('135', plain,
% 4.75/4.99      (![X0 : $i, X2 : $i]:
% 4.75/4.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.75/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.99  thf('136', plain,
% 4.75/4.99      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['134', '135'])).
% 4.75/4.99  thf('137', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['131', '136'])).
% 4.75/4.99  thf('138', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('139', plain,
% 4.75/4.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.75/4.99         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 4.75/4.99          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.75/4.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.75/4.99  thf('140', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['138', '139'])).
% 4.75/4.99  thf('141', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('demod', [status(thm)], ['137', '140'])).
% 4.75/4.99  thf('142', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('clc', [status(thm)], ['89', '90'])).
% 4.75/4.99  thf('143', plain,
% 4.75/4.99      ((((k1_xboole_0) = (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['125', '126', '141', '142'])).
% 4.75/4.99  thf('144', plain,
% 4.75/4.99      (![X38 : $i]:
% 4.75/4.99         ((m1_subset_1 @ X38 @ 
% 4.75/4.99           (k1_zfmisc_1 @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))))
% 4.75/4.99          | ~ (v1_funct_1 @ X38)
% 4.75/4.99          | ~ (v1_relat_1 @ X38))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.75/4.99  thf('145', plain,
% 4.75/4.99      (![X7 : $i, X8 : $i]:
% 4.75/4.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.75/4.99  thf('146', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | (r1_tarski @ X0 @ 
% 4.75/4.99             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['144', '145'])).
% 4.75/4.99  thf('147', plain,
% 4.75/4.99      (![X0 : $i, X2 : $i]:
% 4.75/4.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.75/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.99  thf('148', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (r1_tarski @ 
% 4.75/4.99               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 4.75/4.99          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['146', '147'])).
% 4.75/4.99  thf('149', plain,
% 4.75/4.99      (((~ (r1_tarski @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 4.75/4.99             k1_xboole_0) @ 
% 4.75/4.99            (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 4.75/4.99             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 4.75/4.99             = (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['143', '148'])).
% 4.75/4.99  thf('150', plain,
% 4.75/4.99      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['14'])).
% 4.75/4.99  thf('151', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['132', '133'])).
% 4.75/4.99  thf('152', plain,
% 4.75/4.99      ((((k1_xboole_0) = (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['125', '126', '141', '142'])).
% 4.75/4.99  thf('153', plain,
% 4.75/4.99      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['14'])).
% 4.75/4.99  thf('154', plain,
% 4.75/4.99      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['149', '150', '151', '152', '153'])).
% 4.75/4.99  thf('155', plain,
% 4.75/4.99      (((~ (v1_relat_1 @ k1_xboole_0)
% 4.75/4.99         | ~ (v1_funct_1 @ k1_xboole_0)
% 4.75/4.99         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['95', '154'])).
% 4.75/4.99  thf('156', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('157', plain,
% 4.75/4.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.75/4.99         ((v1_relat_1 @ X18)
% 4.75/4.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.75/4.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.75/4.99  thf('158', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['156', '157'])).
% 4.75/4.99  thf('159', plain,
% 4.75/4.99      (((v1_funct_1 @ sk_B))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['83', '84'])).
% 4.75/4.99  thf('160', plain,
% 4.75/4.99      ((((sk_B) = (k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('clc', [status(thm)], ['89', '90'])).
% 4.75/4.99  thf('161', plain,
% 4.75/4.99      (((v1_funct_1 @ k1_xboole_0))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['159', '160'])).
% 4.75/4.99  thf('162', plain,
% 4.75/4.99      (((~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.75/4.99         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['155', '158', '161'])).
% 4.75/4.99  thf('163', plain,
% 4.75/4.99      (((~ (v1_relat_1 @ k1_xboole_0)
% 4.75/4.99         | ~ (v1_funct_1 @ k1_xboole_0)
% 4.75/4.99         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['94', '162'])).
% 4.75/4.99  thf('164', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['156', '157'])).
% 4.75/4.99  thf('165', plain,
% 4.75/4.99      (((v1_funct_1 @ k1_xboole_0))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['159', '160'])).
% 4.75/4.99  thf('166', plain,
% 4.75/4.99      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 4.75/4.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['163', '164', '165'])).
% 4.75/4.99  thf('167', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['138', '139'])).
% 4.75/4.99  thf('168', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('demod', [status(thm)], ['137', '140'])).
% 4.75/4.99  thf('169', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.99      inference('demod', [status(thm)], ['167', '168'])).
% 4.75/4.99  thf('170', plain,
% 4.75/4.99      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.75/4.99         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 4.75/4.99          | (v1_funct_2 @ X34 @ X32 @ X33)
% 4.75/4.99          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.75/4.99  thf('171', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (((X1) != (k1_xboole_0))
% 4.75/4.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.75/4.99          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['169', '170'])).
% 4.75/4.99  thf('172', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.75/4.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['171'])).
% 4.75/4.99  thf('173', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf('174', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 4.75/4.99      inference('simplify', [status(thm)], ['173'])).
% 4.75/4.99  thf('175', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('176', plain,
% 4.75/4.99      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.75/4.99         (~ (zip_tseitin_0 @ X35 @ X36)
% 4.75/4.99          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 4.75/4.99          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.75/4.99  thf('177', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.75/4.99      inference('sup-', [status(thm)], ['175', '176'])).
% 4.75/4.99  thf('178', plain,
% 4.75/4.99      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.75/4.99      inference('sup-', [status(thm)], ['174', '177'])).
% 4.75/4.99  thf('179', plain,
% 4.75/4.99      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.75/4.99      inference('demod', [status(thm)], ['172', '178'])).
% 4.75/4.99  thf('180', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 4.75/4.99      inference('demod', [status(thm)], ['93', '166', '179'])).
% 4.75/4.99  thf('181', plain,
% 4.75/4.99      (~
% 4.75/4.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 4.75/4.99       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 4.75/4.99       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('split', [status(esa)], ['0'])).
% 4.75/4.99  thf('182', plain,
% 4.75/4.99      (~
% 4.75/4.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.75/4.99      inference('sat_resolution*', [status(thm)], ['10', '180', '181'])).
% 4.75/4.99  thf('183', plain,
% 4.75/4.99      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.99      inference('simpl_trail', [status(thm)], ['1', '182'])).
% 4.75/4.99  thf('184', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf('185', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('186', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('187', plain,
% 4.75/4.99      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['111', '121'])).
% 4.75/4.99  thf('188', plain,
% 4.75/4.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['37', '40'])).
% 4.75/4.99  thf('189', plain,
% 4.75/4.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.75/4.99      inference('sup-', [status(thm)], ['31', '32'])).
% 4.75/4.99  thf('190', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('191', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('192', plain,
% 4.75/4.99      (![X14 : $i]:
% 4.75/4.99         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 4.75/4.99          | ~ (v1_funct_1 @ X14)
% 4.75/4.99          | ~ (v1_relat_1 @ X14))),
% 4.75/4.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.75/4.99  thf('193', plain,
% 4.75/4.99      (![X17 : $i]:
% 4.75/4.99         (~ (v2_funct_1 @ X17)
% 4.75/4.99          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 4.75/4.99          | ~ (v1_funct_1 @ X17)
% 4.75/4.99          | ~ (v1_relat_1 @ X17))),
% 4.75/4.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.75/4.99  thf('194', plain,
% 4.75/4.99      (![X30 : $i, X31 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.75/4.99  thf('195', plain,
% 4.75/4.99      (![X4 : $i, X5 : $i]:
% 4.75/4.99         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 4.75/4.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.75/4.99  thf('196', plain,
% 4.75/4.99      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['195'])).
% 4.75/4.99  thf('197', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.99         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.75/4.99      inference('sup+', [status(thm)], ['194', '196'])).
% 4.75/4.99  thf('198', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | (r1_tarski @ X0 @ 
% 4.75/4.99             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['144', '145'])).
% 4.75/4.99  thf('199', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((r1_tarski @ X0 @ k1_xboole_0)
% 4.75/4.99          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('sup+', [status(thm)], ['197', '198'])).
% 4.75/4.99  thf('200', plain,
% 4.75/4.99      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['134', '135'])).
% 4.75/4.99  thf('201', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.75/4.99          | ((X0) = (k1_xboole_0)))),
% 4.75/4.99      inference('sup-', [status(thm)], ['199', '200'])).
% 4.75/4.99  thf('202', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.75/4.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['193', '201'])).
% 4.75/4.99  thf('203', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.75/4.99      inference('sup-', [status(thm)], ['192', '202'])).
% 4.75/4.99  thf('204', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.75/4.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['203'])).
% 4.75/4.99  thf('205', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         (~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0)
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.75/4.99      inference('sup-', [status(thm)], ['191', '204'])).
% 4.75/4.99  thf('206', plain,
% 4.75/4.99      (![X0 : $i, X1 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.75/4.99          | ~ (v2_funct_1 @ X0)
% 4.75/4.99          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.75/4.99          | ~ (v1_funct_1 @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ X0))),
% 4.75/4.99      inference('simplify', [status(thm)], ['205'])).
% 4.75/4.99  thf('207', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ sk_B @ X0)
% 4.75/4.99          | ~ (v1_relat_1 @ sk_C)
% 4.75/4.99          | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 4.75/4.99          | ~ (v2_funct_1 @ sk_C))),
% 4.75/4.99      inference('sup+', [status(thm)], ['190', '206'])).
% 4.75/4.99  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('211', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 4.75/4.99      inference('demod', [status(thm)], ['207', '208', '209', '210'])).
% 4.75/4.99  thf('212', plain,
% 4.75/4.99      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.99      inference('simpl_trail', [status(thm)], ['1', '182'])).
% 4.75/4.99  thf('213', plain,
% 4.75/4.99      (![X0 : $i]:
% 4.75/4.99         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.75/4.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.75/4.99          | (zip_tseitin_0 @ sk_B @ X0))),
% 4.75/4.99      inference('sup-', [status(thm)], ['211', '212'])).
% 4.75/4.99  thf('214', plain,
% 4.75/4.99      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.75/4.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.75/4.99  thf('215', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 4.75/4.99      inference('demod', [status(thm)], ['213', '214'])).
% 4.75/4.99  thf('216', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 4.75/4.99      inference('demod', [status(thm)], ['189', '215'])).
% 4.75/4.99  thf('217', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.75/4.99      inference('demod', [status(thm)], ['188', '216'])).
% 4.75/4.99  thf('218', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('demod', [status(thm)], ['187', '217'])).
% 4.75/4.99  thf('219', plain,
% 4.75/4.99      (![X38 : $i]:
% 4.75/4.99         ((m1_subset_1 @ X38 @ 
% 4.75/4.99           (k1_zfmisc_1 @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))))
% 4.75/4.99          | ~ (v1_funct_1 @ X38)
% 4.75/4.99          | ~ (v1_relat_1 @ X38))),
% 4.75/4.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.75/4.99  thf('220', plain,
% 4.75/4.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99         (k1_zfmisc_1 @ 
% 4.75/4.99          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 4.75/4.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.75/4.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.75/4.99      inference('sup+', [status(thm)], ['218', '219'])).
% 4.75/4.99  thf('221', plain,
% 4.75/4.99      ((~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.75/4.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99           (k1_zfmisc_1 @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['186', '220'])).
% 4.75/4.99  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('224', plain,
% 4.75/4.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.75/4.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99           (k1_zfmisc_1 @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 4.75/4.99      inference('demod', [status(thm)], ['221', '222', '223'])).
% 4.75/4.99  thf('225', plain,
% 4.75/4.99      ((~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99           (k1_zfmisc_1 @ 
% 4.75/4.99            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 4.75/4.99      inference('sup-', [status(thm)], ['185', '224'])).
% 4.75/4.99  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('228', plain,
% 4.75/4.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99        (k1_zfmisc_1 @ 
% 4.75/4.99         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['225', '226', '227'])).
% 4.75/4.99  thf('229', plain,
% 4.75/4.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 4.75/4.99        | ~ (v1_relat_1 @ sk_C)
% 4.75/4.99        | ~ (v1_funct_1 @ sk_C)
% 4.75/4.99        | ~ (v2_funct_1 @ sk_C))),
% 4.75/4.99      inference('sup+', [status(thm)], ['184', '228'])).
% 4.75/4.99  thf('230', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.75/4.99      inference('sup+', [status(thm)], ['58', '59'])).
% 4.75/4.99  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.75/4.99  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 4.75/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.99  thf('234', plain,
% 4.75/4.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.75/4.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.99      inference('demod', [status(thm)], ['229', '230', '231', '232', '233'])).
% 4.75/4.99  thf('235', plain, ($false), inference('demod', [status(thm)], ['183', '234'])).
% 4.75/4.99  
% 4.75/4.99  % SZS output end Refutation
% 4.75/4.99  
% 4.75/5.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
