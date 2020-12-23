%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gyrqMaVA30

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:48 EST 2020

% Result     : Theorem 5.97s
% Output     : Refutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  247 (14063 expanded)
%              Number of leaves         :   39 (4056 expanded)
%              Depth                    :   28
%              Number of atoms          : 2043 (205719 expanded)
%              Number of equality atoms :  123 (9582 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
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

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_B @ sk_C )
      | ( sk_B = sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['26','29'])).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('46',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['58','63','64','65','66'])).

thf('68',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','69'])).

thf('71',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('72',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('79',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('85',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','82','85','88','91'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','69'])).

thf('94',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','94','95'])).

thf('97',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('101',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('105',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('106',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('109',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['100','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('129',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('131',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['99','131'])).

thf('133',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('134',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('135',plain,
    ( ( ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','94','95'])).

thf('137',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('138',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('139',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,(
    ! [X28: $i] :
      ( zip_tseitin_0 @ X28 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('149',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['145','151'])).

thf('153',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['137','152'])).

thf('154',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('157',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['154','161'])).

thf('163',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('164',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('166',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('167',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('168',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('169',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['96','153','169'])).

thf('171',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('172',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','170','171'])).

thf('173',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','172'])).

thf('174',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('175',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('176',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('178',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['175','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['174','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('192',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('193',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('195',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('197',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('199',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','170','171'])).

thf('201',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','201','202','203','204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['173','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gyrqMaVA30
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.97/6.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.97/6.18  % Solved by: fo/fo7.sh
% 5.97/6.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.97/6.18  % done 5211 iterations in 5.703s
% 5.97/6.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.97/6.18  % SZS output start Refutation
% 5.97/6.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.97/6.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.97/6.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.97/6.18  thf(sk_A_type, type, sk_A: $i).
% 5.97/6.18  thf(sk_B_type, type, sk_B: $i).
% 5.97/6.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.97/6.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.97/6.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.97/6.18  thf(sk_C_type, type, sk_C: $i).
% 5.97/6.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.97/6.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.97/6.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.97/6.18  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.97/6.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.97/6.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.97/6.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.97/6.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.97/6.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.97/6.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.97/6.18  thf(t31_funct_2, conjecture,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.97/6.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.97/6.18       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.97/6.18         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.97/6.18           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.97/6.18           ( m1_subset_1 @
% 5.97/6.18             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.97/6.18  thf(zf_stmt_0, negated_conjecture,
% 5.97/6.18    (~( ![A:$i,B:$i,C:$i]:
% 5.97/6.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.97/6.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.97/6.18          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.97/6.18            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.97/6.18              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.97/6.18              ( m1_subset_1 @
% 5.97/6.18                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 5.97/6.18    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 5.97/6.18  thf('0', plain,
% 5.97/6.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.97/6.18        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 5.97/6.18        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('1', plain,
% 5.97/6.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf('2', plain,
% 5.97/6.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf(cc2_relat_1, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( v1_relat_1 @ A ) =>
% 5.97/6.18       ( ![B:$i]:
% 5.97/6.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.97/6.18  thf('3', plain,
% 5.97/6.18      (![X14 : $i, X15 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 5.97/6.18          | (v1_relat_1 @ X14)
% 5.97/6.18          | ~ (v1_relat_1 @ X15))),
% 5.97/6.18      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.97/6.18  thf('4', plain,
% 5.97/6.18      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.97/6.18      inference('sup-', [status(thm)], ['2', '3'])).
% 5.97/6.18  thf(fc6_relat_1, axiom,
% 5.97/6.18    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.97/6.18  thf('5', plain,
% 5.97/6.18      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 5.97/6.18      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.97/6.18  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf(dt_k2_funct_1, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.97/6.18       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.97/6.18         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.97/6.18  thf('7', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('8', plain,
% 5.97/6.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf('9', plain,
% 5.97/6.18      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['7', '8'])).
% 5.97/6.18  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('11', plain,
% 5.97/6.18      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.97/6.18      inference('demod', [status(thm)], ['9', '10'])).
% 5.97/6.18  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['6', '11'])).
% 5.97/6.18  thf('13', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf(d1_funct_2, axiom,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.97/6.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.97/6.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.97/6.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.97/6.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.97/6.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.97/6.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.97/6.18  thf(zf_stmt_1, axiom,
% 5.97/6.18    (![B:$i,A:$i]:
% 5.97/6.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.97/6.18       ( zip_tseitin_0 @ B @ A ) ))).
% 5.97/6.18  thf('14', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf('15', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf(t113_zfmisc_1, axiom,
% 5.97/6.18    (![A:$i,B:$i]:
% 5.97/6.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.97/6.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.97/6.18  thf('16', plain,
% 5.97/6.18      (![X5 : $i, X6 : $i]:
% 5.97/6.18         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.97/6.18  thf('17', plain,
% 5.97/6.18      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['16'])).
% 5.97/6.18  thf('18', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.97/6.18         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.97/6.18      inference('sup+', [status(thm)], ['15', '17'])).
% 5.97/6.18  thf('19', plain,
% 5.97/6.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('20', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.97/6.18          | (zip_tseitin_0 @ sk_B @ X0))),
% 5.97/6.18      inference('sup+', [status(thm)], ['18', '19'])).
% 5.97/6.18  thf('21', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.97/6.18         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 5.97/6.18          | (zip_tseitin_0 @ X0 @ X2)
% 5.97/6.18          | (zip_tseitin_0 @ sk_B @ X1))),
% 5.97/6.18      inference('sup+', [status(thm)], ['14', '20'])).
% 5.97/6.18  thf('22', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ sk_B @ X0)
% 5.97/6.18          | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))),
% 5.97/6.18      inference('eq_fact', [status(thm)], ['21'])).
% 5.97/6.18  thf(t3_subset, axiom,
% 5.97/6.18    (![A:$i,B:$i]:
% 5.97/6.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.97/6.18  thf('23', plain,
% 5.97/6.18      (![X8 : $i, X9 : $i]:
% 5.97/6.18         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 5.97/6.18      inference('cnf', [status(esa)], [t3_subset])).
% 5.97/6.18  thf('24', plain,
% 5.97/6.18      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 5.97/6.18      inference('sup-', [status(thm)], ['22', '23'])).
% 5.97/6.18  thf(d10_xboole_0, axiom,
% 5.97/6.18    (![A:$i,B:$i]:
% 5.97/6.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.97/6.18  thf('25', plain,
% 5.97/6.18      (![X0 : $i, X2 : $i]:
% 5.97/6.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.97/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.97/6.18  thf('26', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ sk_B @ X0)
% 5.97/6.18          | ~ (r1_tarski @ sk_B @ sk_C)
% 5.97/6.18          | ((sk_B) = (sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['24', '25'])).
% 5.97/6.18  thf('27', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.97/6.18  thf('28', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.97/6.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.97/6.18  thf('29', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.97/6.18         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 5.97/6.18      inference('sup+', [status(thm)], ['27', '28'])).
% 5.97/6.18  thf('30', plain,
% 5.97/6.18      (![X0 : $i]: (((sk_B) = (sk_C)) | (zip_tseitin_0 @ sk_B @ X0))),
% 5.97/6.18      inference('clc', [status(thm)], ['26', '29'])).
% 5.97/6.18  thf('31', plain,
% 5.97/6.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.97/6.18  thf(zf_stmt_3, axiom,
% 5.97/6.18    (![C:$i,B:$i,A:$i]:
% 5.97/6.18     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.97/6.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.97/6.18  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.97/6.18  thf(zf_stmt_5, axiom,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.97/6.18       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.97/6.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.97/6.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.97/6.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.97/6.18  thf('32', plain,
% 5.97/6.18      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.97/6.18         (~ (zip_tseitin_0 @ X33 @ X34)
% 5.97/6.18          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 5.97/6.18          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.97/6.18  thf('33', plain,
% 5.97/6.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['31', '32'])).
% 5.97/6.18  thf('34', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['30', '33'])).
% 5.97/6.18  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('36', plain,
% 5.97/6.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.97/6.18         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 5.97/6.18          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 5.97/6.18          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.97/6.18  thf('37', plain,
% 5.97/6.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 5.97/6.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['35', '36'])).
% 5.97/6.18  thf('38', plain,
% 5.97/6.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf(redefinition_k1_relset_1, axiom,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.97/6.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.97/6.18  thf('39', plain,
% 5.97/6.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.97/6.18         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.97/6.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.97/6.18  thf('40', plain,
% 5.97/6.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.97/6.18      inference('sup-', [status(thm)], ['38', '39'])).
% 5.97/6.18  thf('41', plain,
% 5.97/6.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('demod', [status(thm)], ['37', '40'])).
% 5.97/6.18  thf('42', plain, ((((sk_B) = (sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['34', '41'])).
% 5.97/6.18  thf(t55_funct_1, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.97/6.18       ( ( v2_funct_1 @ A ) =>
% 5.97/6.18         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.97/6.18           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.97/6.18  thf('43', plain,
% 5.97/6.18      (![X21 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X21)
% 5.97/6.18          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 5.97/6.18          | ~ (v1_funct_1 @ X21)
% 5.97/6.18          | ~ (v1_relat_1 @ X21))),
% 5.97/6.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.97/6.18  thf('44', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('45', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('46', plain,
% 5.97/6.18      (![X21 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X21)
% 5.97/6.18          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 5.97/6.18          | ~ (v1_funct_1 @ X21)
% 5.97/6.18          | ~ (v1_relat_1 @ X21))),
% 5.97/6.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.97/6.18  thf('47', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.97/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.97/6.18  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.97/6.18      inference('simplify', [status(thm)], ['47'])).
% 5.97/6.18  thf(t4_funct_2, axiom,
% 5.97/6.18    (![A:$i,B:$i]:
% 5.97/6.18     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.97/6.18       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 5.97/6.18         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 5.97/6.18           ( m1_subset_1 @
% 5.97/6.18             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 5.97/6.18  thf('49', plain,
% 5.97/6.18      (![X36 : $i, X37 : $i]:
% 5.97/6.18         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 5.97/6.18          | (v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ X37)
% 5.97/6.18          | ~ (v1_funct_1 @ X36)
% 5.97/6.18          | ~ (v1_relat_1 @ X36))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.97/6.18  thf('50', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['48', '49'])).
% 5.97/6.18  thf('51', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['46', '50'])).
% 5.97/6.18  thf('52', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['45', '51'])).
% 5.97/6.18  thf('53', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['52'])).
% 5.97/6.18  thf('54', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['44', '53'])).
% 5.97/6.18  thf('55', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['54'])).
% 5.97/6.18  thf('56', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18           (k1_relat_1 @ X0))
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0))),
% 5.97/6.18      inference('sup+', [status(thm)], ['43', '55'])).
% 5.97/6.18  thf('57', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18             (k1_relat_1 @ X0)))),
% 5.97/6.18      inference('simplify', [status(thm)], ['56'])).
% 5.97/6.18  thf('58', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 5.97/6.18        | ((sk_B) = (sk_C))
% 5.97/6.18        | ~ (v1_relat_1 @ sk_C)
% 5.97/6.18        | ~ (v1_funct_1 @ sk_C)
% 5.97/6.18        | ~ (v2_funct_1 @ sk_C))),
% 5.97/6.18      inference('sup+', [status(thm)], ['42', '57'])).
% 5.97/6.18  thf('59', plain,
% 5.97/6.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf(redefinition_k2_relset_1, axiom,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.97/6.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.97/6.18  thf('60', plain,
% 5.97/6.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.97/6.18         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 5.97/6.18          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.97/6.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.97/6.18  thf('61', plain,
% 5.97/6.18      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 5.97/6.18      inference('sup-', [status(thm)], ['59', '60'])).
% 5.97/6.18  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('63', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.97/6.18      inference('sup+', [status(thm)], ['61', '62'])).
% 5.97/6.18  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('67', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 5.97/6.18      inference('demod', [status(thm)], ['58', '63', '64', '65', '66'])).
% 5.97/6.18  thf('68', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf('69', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('70', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['13', '69'])).
% 5.97/6.18  thf('71', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('72', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf('73', plain,
% 5.97/6.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['31', '32'])).
% 5.97/6.18  thf('74', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['72', '73'])).
% 5.97/6.18  thf('75', plain,
% 5.97/6.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('demod', [status(thm)], ['37', '40'])).
% 5.97/6.18  thf('76', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['74', '75'])).
% 5.97/6.18  thf('77', plain,
% 5.97/6.18      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['71', '76'])).
% 5.97/6.18  thf('78', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18             (k1_relat_1 @ X0)))),
% 5.97/6.18      inference('simplify', [status(thm)], ['56'])).
% 5.97/6.18  thf('79', plain,
% 5.97/6.18      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 5.97/6.18         | ((sk_B) = (k1_xboole_0))
% 5.97/6.18         | ~ (v1_relat_1 @ sk_B)
% 5.97/6.18         | ~ (v1_funct_1 @ sk_B)
% 5.97/6.18         | ~ (v2_funct_1 @ sk_B)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['77', '78'])).
% 5.97/6.18  thf('80', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.97/6.18      inference('sup+', [status(thm)], ['61', '62'])).
% 5.97/6.18  thf('82', plain,
% 5.97/6.18      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['80', '81'])).
% 5.97/6.18  thf('83', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('85', plain,
% 5.97/6.18      (((v1_relat_1 @ sk_B))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['83', '84'])).
% 5.97/6.18  thf('86', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('88', plain,
% 5.97/6.18      (((v1_funct_1 @ sk_B))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['86', '87'])).
% 5.97/6.18  thf('89', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('91', plain,
% 5.97/6.18      (((v2_funct_1 @ sk_B))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['89', '90'])).
% 5.97/6.18  thf('92', plain,
% 5.97/6.18      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 5.97/6.18         | ((sk_B) = (k1_xboole_0))))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['79', '82', '85', '88', '91'])).
% 5.97/6.18  thf('93', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['13', '69'])).
% 5.97/6.18  thf('94', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('95', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('96', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['70', '94', '95'])).
% 5.97/6.18  thf('97', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('98', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('99', plain,
% 5.97/6.18      ((((k1_xboole_0) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['97', '98'])).
% 5.97/6.18  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.97/6.18      inference('sup+', [status(thm)], ['61', '62'])).
% 5.97/6.18  thf('101', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('102', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('103', plain,
% 5.97/6.18      (![X21 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X21)
% 5.97/6.18          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 5.97/6.18          | ~ (v1_funct_1 @ X21)
% 5.97/6.18          | ~ (v1_relat_1 @ X21))),
% 5.97/6.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.97/6.18  thf('104', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf('105', plain,
% 5.97/6.18      (![X5 : $i, X6 : $i]:
% 5.97/6.18         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.97/6.18  thf('106', plain,
% 5.97/6.18      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['105'])).
% 5.97/6.18  thf('107', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.97/6.18         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.97/6.18      inference('sup+', [status(thm)], ['104', '106'])).
% 5.97/6.18  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.97/6.18      inference('simplify', [status(thm)], ['47'])).
% 5.97/6.18  thf('109', plain,
% 5.97/6.18      (![X36 : $i, X37 : $i]:
% 5.97/6.18         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 5.97/6.18          | (m1_subset_1 @ X36 @ 
% 5.97/6.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 5.97/6.18          | ~ (v1_funct_1 @ X36)
% 5.97/6.18          | ~ (v1_relat_1 @ X36))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.97/6.18  thf('110', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | (m1_subset_1 @ X0 @ 
% 5.97/6.18             (k1_zfmisc_1 @ 
% 5.97/6.18              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['108', '109'])).
% 5.97/6.18  thf('111', plain,
% 5.97/6.18      (![X8 : $i, X9 : $i]:
% 5.97/6.18         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 5.97/6.18      inference('cnf', [status(esa)], [t3_subset])).
% 5.97/6.18  thf('112', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (r1_tarski @ X0 @ 
% 5.97/6.18             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['110', '111'])).
% 5.97/6.18  thf('113', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((r1_tarski @ X0 @ k1_xboole_0)
% 5.97/6.18          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0))),
% 5.97/6.18      inference('sup+', [status(thm)], ['107', '112'])).
% 5.97/6.18  thf('114', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.97/6.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.97/6.18  thf('115', plain,
% 5.97/6.18      (![X0 : $i, X2 : $i]:
% 5.97/6.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.97/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.97/6.18  thf('116', plain,
% 5.97/6.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['114', '115'])).
% 5.97/6.18  thf('117', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 5.97/6.18          | ((X0) = (k1_xboole_0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['113', '116'])).
% 5.97/6.18  thf('118', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['103', '117'])).
% 5.97/6.18  thf('119', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 5.97/6.18      inference('sup-', [status(thm)], ['102', '118'])).
% 5.97/6.18  thf('120', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 5.97/6.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['119'])).
% 5.97/6.18  thf('121', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 5.97/6.18      inference('sup-', [status(thm)], ['101', '120'])).
% 5.97/6.18  thf('122', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['121'])).
% 5.97/6.18  thf('123', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ sk_B @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ sk_C)
% 5.97/6.18          | ~ (v1_funct_1 @ sk_C)
% 5.97/6.18          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 5.97/6.18          | ~ (v2_funct_1 @ sk_C))),
% 5.97/6.18      inference('sup+', [status(thm)], ['100', '122'])).
% 5.97/6.18  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('127', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 5.97/6.18      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 5.97/6.18  thf('128', plain,
% 5.97/6.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['31', '32'])).
% 5.97/6.18  thf('129', plain,
% 5.97/6.18      ((((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 5.97/6.18        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['127', '128'])).
% 5.97/6.18  thf('130', plain,
% 5.97/6.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('demod', [status(thm)], ['37', '40'])).
% 5.97/6.18  thf('131', plain,
% 5.97/6.18      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['129', '130'])).
% 5.97/6.18  thf('132', plain,
% 5.97/6.18      (((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.97/6.18         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['99', '131'])).
% 5.97/6.18  thf('133', plain,
% 5.97/6.18      ((((k1_xboole_0) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['97', '98'])).
% 5.97/6.18  thf(t60_relat_1, axiom,
% 5.97/6.18    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 5.97/6.18     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.97/6.18  thf('134', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 5.97/6.18  thf('135', plain,
% 5.97/6.18      (((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.97/6.18         | ((sk_A) = (k1_xboole_0))))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['132', '133', '134'])).
% 5.97/6.18  thf('136', plain,
% 5.97/6.18      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['70', '94', '95'])).
% 5.97/6.18  thf('137', plain,
% 5.97/6.18      (((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 5.97/6.18         | ((sk_A) = (k1_xboole_0))))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['135', '136'])).
% 5.97/6.18  thf(t4_subset_1, axiom,
% 5.97/6.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.97/6.18  thf('138', plain,
% 5.97/6.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.97/6.18  thf('139', plain,
% 5.97/6.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.97/6.18         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.97/6.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.97/6.18  thf('140', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['138', '139'])).
% 5.97/6.18  thf('141', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 5.97/6.18  thf('142', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.97/6.18      inference('demod', [status(thm)], ['140', '141'])).
% 5.97/6.18  thf('143', plain,
% 5.97/6.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.97/6.18         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 5.97/6.18          | (v1_funct_2 @ X32 @ X30 @ X31)
% 5.97/6.18          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.97/6.18  thf('144', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (((X1) != (k1_xboole_0))
% 5.97/6.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 5.97/6.18          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['142', '143'])).
% 5.97/6.18  thf('145', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 5.97/6.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['144'])).
% 5.97/6.18  thf('146', plain,
% 5.97/6.18      (![X28 : $i, X29 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ X28 @ X29) | ((X29) != (k1_xboole_0)))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.97/6.18  thf('147', plain, (![X28 : $i]: (zip_tseitin_0 @ X28 @ k1_xboole_0)),
% 5.97/6.18      inference('simplify', [status(thm)], ['146'])).
% 5.97/6.18  thf('148', plain,
% 5.97/6.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.97/6.18  thf('149', plain,
% 5.97/6.18      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.97/6.18         (~ (zip_tseitin_0 @ X33 @ X34)
% 5.97/6.18          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 5.97/6.18          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.97/6.18  thf('150', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 5.97/6.18      inference('sup-', [status(thm)], ['148', '149'])).
% 5.97/6.18  thf('151', plain,
% 5.97/6.18      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 5.97/6.18      inference('sup-', [status(thm)], ['147', '150'])).
% 5.97/6.18  thf('152', plain,
% 5.97/6.18      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.97/6.18      inference('demod', [status(thm)], ['145', '151'])).
% 5.97/6.18  thf('153', plain,
% 5.97/6.18      ((((sk_A) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['137', '152'])).
% 5.97/6.18  thf('154', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('155', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.97/6.18      inference('sup+', [status(thm)], ['61', '62'])).
% 5.97/6.18  thf('156', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 5.97/6.18             (k1_relat_1 @ X0)))),
% 5.97/6.18      inference('simplify', [status(thm)], ['56'])).
% 5.97/6.18  thf('157', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 5.97/6.18        | ~ (v1_relat_1 @ sk_C)
% 5.97/6.18        | ~ (v1_funct_1 @ sk_C)
% 5.97/6.18        | ~ (v2_funct_1 @ sk_C))),
% 5.97/6.18      inference('sup+', [status(thm)], ['155', '156'])).
% 5.97/6.18  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('161', plain,
% 5.97/6.18      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 5.97/6.18      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 5.97/6.18  thf('162', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ (k1_relat_1 @ sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['154', '161'])).
% 5.97/6.18  thf('163', plain,
% 5.97/6.18      ((((sk_B) = (sk_C)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['67', '68'])).
% 5.97/6.18  thf('164', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ (k1_relat_1 @ sk_B)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['162', '163'])).
% 5.97/6.18  thf('165', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('166', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('167', plain,
% 5.97/6.18      ((((sk_B) = (k1_xboole_0)))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['92', '93'])).
% 5.97/6.18  thf('168', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 5.97/6.18  thf('169', plain,
% 5.97/6.18      (((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ k1_xboole_0))
% 5.97/6.18         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 5.97/6.18  thf('170', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['96', '153', '169'])).
% 5.97/6.18  thf('171', plain,
% 5.97/6.18      (~
% 5.97/6.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 5.97/6.18       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 5.97/6.18       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf('172', plain,
% 5.97/6.18      (~
% 5.97/6.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 5.97/6.18      inference('sat_resolution*', [status(thm)], ['12', '170', '171'])).
% 5.97/6.18  thf('173', plain,
% 5.97/6.18      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.97/6.18      inference('simpl_trail', [status(thm)], ['1', '172'])).
% 5.97/6.18  thf('174', plain,
% 5.97/6.18      (![X21 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X21)
% 5.97/6.18          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 5.97/6.18          | ~ (v1_funct_1 @ X21)
% 5.97/6.18          | ~ (v1_relat_1 @ X21))),
% 5.97/6.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.97/6.18  thf('175', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.97/6.18      inference('sup+', [status(thm)], ['61', '62'])).
% 5.97/6.18  thf('176', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('177', plain,
% 5.97/6.18      (![X20 : $i]:
% 5.97/6.18         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 5.97/6.18          | ~ (v1_funct_1 @ X20)
% 5.97/6.18          | ~ (v1_relat_1 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.97/6.18  thf('178', plain,
% 5.97/6.18      (![X21 : $i]:
% 5.97/6.18         (~ (v2_funct_1 @ X21)
% 5.97/6.18          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 5.97/6.18          | ~ (v1_funct_1 @ X21)
% 5.97/6.18          | ~ (v1_relat_1 @ X21))),
% 5.97/6.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.97/6.18  thf('179', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | (m1_subset_1 @ X0 @ 
% 5.97/6.18             (k1_zfmisc_1 @ 
% 5.97/6.18              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['108', '109'])).
% 5.97/6.18  thf('180', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.97/6.18           (k1_zfmisc_1 @ 
% 5.97/6.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.97/6.18      inference('sup+', [status(thm)], ['178', '179'])).
% 5.97/6.18  thf('181', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.97/6.18             (k1_zfmisc_1 @ 
% 5.97/6.18              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.97/6.18               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['177', '180'])).
% 5.97/6.18  thf('182', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.97/6.18           (k1_zfmisc_1 @ 
% 5.97/6.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['181'])).
% 5.97/6.18  thf('183', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.97/6.18             (k1_zfmisc_1 @ 
% 5.97/6.18              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.97/6.18               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['176', '182'])).
% 5.97/6.18  thf('184', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.97/6.18           (k1_zfmisc_1 @ 
% 5.97/6.18            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.97/6.18          | ~ (v2_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_funct_1 @ X0)
% 5.97/6.18          | ~ (v1_relat_1 @ X0))),
% 5.97/6.18      inference('simplify', [status(thm)], ['183'])).
% 5.97/6.18  thf('185', plain,
% 5.97/6.18      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18         (k1_zfmisc_1 @ 
% 5.97/6.18          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 5.97/6.18        | ~ (v1_relat_1 @ sk_C)
% 5.97/6.18        | ~ (v1_funct_1 @ sk_C)
% 5.97/6.18        | ~ (v2_funct_1 @ sk_C))),
% 5.97/6.18      inference('sup+', [status(thm)], ['175', '184'])).
% 5.97/6.18  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('189', plain,
% 5.97/6.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18        (k1_zfmisc_1 @ 
% 5.97/6.18         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 5.97/6.18      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 5.97/6.18  thf('190', plain,
% 5.97/6.18      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 5.97/6.18        | ~ (v1_relat_1 @ sk_C)
% 5.97/6.18        | ~ (v1_funct_1 @ sk_C)
% 5.97/6.18        | ~ (v2_funct_1 @ sk_C))),
% 5.97/6.18      inference('sup+', [status(thm)], ['174', '189'])).
% 5.97/6.18  thf('191', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 5.97/6.18      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 5.97/6.18  thf('192', plain,
% 5.97/6.18      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('split', [status(esa)], ['0'])).
% 5.97/6.18  thf('193', plain,
% 5.97/6.18      ((![X0 : $i]:
% 5.97/6.18          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 5.97/6.18              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.97/6.18           | (zip_tseitin_0 @ sk_B @ X0)))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['191', '192'])).
% 5.97/6.18  thf('194', plain,
% 5.97/6.18      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.97/6.18  thf('195', plain,
% 5.97/6.18      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('demod', [status(thm)], ['193', '194'])).
% 5.97/6.18  thf('196', plain,
% 5.97/6.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['31', '32'])).
% 5.97/6.18  thf('197', plain,
% 5.97/6.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['195', '196'])).
% 5.97/6.18  thf('198', plain,
% 5.97/6.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 5.97/6.18      inference('demod', [status(thm)], ['37', '40'])).
% 5.97/6.18  thf('199', plain,
% 5.97/6.18      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 5.97/6.18         <= (~
% 5.97/6.18             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['197', '198'])).
% 5.97/6.18  thf('200', plain,
% 5.97/6.18      (~
% 5.97/6.18       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 5.97/6.18      inference('sat_resolution*', [status(thm)], ['12', '170', '171'])).
% 5.97/6.18  thf('201', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.97/6.18      inference('simpl_trail', [status(thm)], ['199', '200'])).
% 5.97/6.18  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 5.97/6.18      inference('demod', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('205', plain,
% 5.97/6.18      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.97/6.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.97/6.18      inference('demod', [status(thm)], ['190', '201', '202', '203', '204'])).
% 5.97/6.18  thf('206', plain, ($false), inference('demod', [status(thm)], ['173', '205'])).
% 5.97/6.18  
% 5.97/6.18  % SZS output end Refutation
% 5.97/6.18  
% 5.97/6.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
