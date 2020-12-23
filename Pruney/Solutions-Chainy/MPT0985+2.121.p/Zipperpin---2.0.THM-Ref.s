%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjz1xAXBqK

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 7.25s
% Output     : Refutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 492 expanded)
%              Number of leaves         :   41 ( 158 expanded)
%              Depth                    :   21
%              Number of atoms          : 1389 (7651 expanded)
%              Number of equality atoms :   74 ( 330 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( sk_C @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( v1_funct_2 @ ( sk_C @ X30 @ X31 ) @ X31 @ X30 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','58'])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('61',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('63',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('65',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['63','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','82','83'])).

thf('85',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('87',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('90',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['86','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('104',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('108',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('110',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','82','83'])).

thf('112',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('114',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','112','113','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['85','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjz1xAXBqK
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.25/7.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.25/7.45  % Solved by: fo/fo7.sh
% 7.25/7.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.25/7.45  % done 6061 iterations in 6.987s
% 7.25/7.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.25/7.45  % SZS output start Refutation
% 7.25/7.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.25/7.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 7.25/7.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.25/7.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.25/7.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.25/7.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.25/7.45  thf(sk_A_type, type, sk_A: $i).
% 7.25/7.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.25/7.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.25/7.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.25/7.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.25/7.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.25/7.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.25/7.45  thf(sk_B_type, type, sk_B: $i).
% 7.25/7.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.25/7.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.25/7.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.25/7.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.25/7.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.25/7.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 7.25/7.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.25/7.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.25/7.45  thf(t31_funct_2, conjecture,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.25/7.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.25/7.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 7.25/7.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 7.25/7.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 7.25/7.45           ( m1_subset_1 @
% 7.25/7.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 7.25/7.45  thf(zf_stmt_0, negated_conjecture,
% 7.25/7.45    (~( ![A:$i,B:$i,C:$i]:
% 7.25/7.45        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.25/7.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.25/7.45          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 7.25/7.45            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 7.25/7.45              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 7.25/7.45              ( m1_subset_1 @
% 7.25/7.45                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 7.25/7.45    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 7.25/7.45  thf('0', plain,
% 7.25/7.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 7.25/7.45        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 7.25/7.45        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('1', plain,
% 7.25/7.45      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf('2', plain,
% 7.25/7.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf(cc1_relset_1, axiom,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.25/7.45       ( v1_relat_1 @ C ) ))).
% 7.25/7.45  thf('3', plain,
% 7.25/7.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.25/7.45         ((v1_relat_1 @ X13)
% 7.25/7.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 7.25/7.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.25/7.45  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 7.25/7.45      inference('sup-', [status(thm)], ['2', '3'])).
% 7.25/7.45  thf(dt_k2_funct_1, axiom,
% 7.25/7.45    (![A:$i]:
% 7.25/7.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.25/7.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 7.25/7.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 7.25/7.45  thf('5', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf('6', plain,
% 7.25/7.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 7.25/7.45         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf('7', plain,
% 7.25/7.45      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 7.25/7.45         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['5', '6'])).
% 7.25/7.45  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('9', plain,
% 7.25/7.45      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 7.25/7.45      inference('demod', [status(thm)], ['7', '8'])).
% 7.25/7.45  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['4', '9'])).
% 7.25/7.45  thf('11', plain,
% 7.25/7.45      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf(d1_funct_2, axiom,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.25/7.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.25/7.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.25/7.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.25/7.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.25/7.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.25/7.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.25/7.45  thf(zf_stmt_1, axiom,
% 7.25/7.45    (![B:$i,A:$i]:
% 7.25/7.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.25/7.45       ( zip_tseitin_0 @ B @ A ) ))).
% 7.25/7.45  thf('12', plain,
% 7.25/7.45      (![X22 : $i, X23 : $i]:
% 7.25/7.45         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.25/7.45  thf(t113_zfmisc_1, axiom,
% 7.25/7.45    (![A:$i,B:$i]:
% 7.25/7.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 7.25/7.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 7.25/7.45  thf('13', plain,
% 7.25/7.45      (![X5 : $i, X6 : $i]:
% 7.25/7.45         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 7.25/7.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 7.25/7.45  thf('14', plain,
% 7.25/7.45      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['13'])).
% 7.25/7.45  thf(rc1_funct_2, axiom,
% 7.25/7.45    (![A:$i,B:$i]:
% 7.25/7.45     ( ?[C:$i]:
% 7.25/7.45       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 7.25/7.45         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 7.25/7.45         ( v1_relat_1 @ C ) & 
% 7.25/7.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 7.25/7.45  thf('15', plain,
% 7.25/7.45      (![X30 : $i, X31 : $i]:
% 7.25/7.45         (m1_subset_1 @ (sk_C @ X30 @ X31) @ 
% 7.25/7.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))),
% 7.25/7.45      inference('cnf', [status(esa)], [rc1_funct_2])).
% 7.25/7.45  thf('16', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (m1_subset_1 @ (sk_C @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 7.25/7.45      inference('sup+', [status(thm)], ['14', '15'])).
% 7.25/7.45  thf(t3_subset, axiom,
% 7.25/7.45    (![A:$i,B:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.25/7.45  thf('17', plain,
% 7.25/7.45      (![X7 : $i, X8 : $i]:
% 7.25/7.45         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 7.25/7.45      inference('cnf', [status(esa)], [t3_subset])).
% 7.25/7.45  thf('18', plain,
% 7.25/7.45      (![X0 : $i]: (r1_tarski @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)),
% 7.25/7.45      inference('sup-', [status(thm)], ['16', '17'])).
% 7.25/7.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.25/7.45  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 7.25/7.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.25/7.45  thf(d10_xboole_0, axiom,
% 7.25/7.45    (![A:$i,B:$i]:
% 7.25/7.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.25/7.45  thf('20', plain,
% 7.25/7.45      (![X0 : $i, X2 : $i]:
% 7.25/7.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.25/7.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.25/7.45  thf('21', plain,
% 7.25/7.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['19', '20'])).
% 7.25/7.45  thf('22', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.25/7.45      inference('sup-', [status(thm)], ['18', '21'])).
% 7.25/7.45  thf('23', plain,
% 7.25/7.45      (![X30 : $i, X31 : $i]: (v1_funct_2 @ (sk_C @ X30 @ X31) @ X31 @ X30)),
% 7.25/7.45      inference('cnf', [status(esa)], [rc1_funct_2])).
% 7.25/7.45  thf('24', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 7.25/7.45      inference('sup+', [status(thm)], ['22', '23'])).
% 7.25/7.45  thf('25', plain,
% 7.25/7.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.25/7.45         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 7.25/7.45      inference('sup+', [status(thm)], ['12', '24'])).
% 7.25/7.45  thf('26', plain,
% 7.25/7.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf(redefinition_k2_relset_1, axiom,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.25/7.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.25/7.45  thf('27', plain,
% 7.25/7.45      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.25/7.45         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 7.25/7.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 7.25/7.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.25/7.45  thf('28', plain,
% 7.25/7.45      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 7.25/7.45      inference('sup-', [status(thm)], ['26', '27'])).
% 7.25/7.45  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('30', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 7.25/7.45      inference('sup+', [status(thm)], ['28', '29'])).
% 7.25/7.45  thf('31', plain,
% 7.25/7.45      (![X22 : $i, X23 : $i]:
% 7.25/7.45         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.25/7.45  thf('32', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf(t55_funct_1, axiom,
% 7.25/7.45    (![A:$i]:
% 7.25/7.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.25/7.45       ( ( v2_funct_1 @ A ) =>
% 7.25/7.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 7.25/7.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 7.25/7.45  thf('33', plain,
% 7.25/7.45      (![X12 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X12)
% 7.25/7.45          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 7.25/7.45          | ~ (v1_funct_1 @ X12)
% 7.25/7.45          | ~ (v1_relat_1 @ X12))),
% 7.25/7.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.25/7.45  thf(t64_relat_1, axiom,
% 7.25/7.45    (![A:$i]:
% 7.25/7.45     ( ( v1_relat_1 @ A ) =>
% 7.25/7.45       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 7.25/7.45           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 7.25/7.45         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 7.25/7.45  thf('34', plain,
% 7.25/7.45      (![X10 : $i]:
% 7.25/7.45         (((k1_relat_1 @ X10) != (k1_xboole_0))
% 7.25/7.45          | ((X10) = (k1_xboole_0))
% 7.25/7.45          | ~ (v1_relat_1 @ X10))),
% 7.25/7.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 7.25/7.45  thf('35', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['33', '34'])).
% 7.25/7.45  thf('36', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['32', '35'])).
% 7.25/7.45  thf('37', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['36'])).
% 7.25/7.45  thf('38', plain,
% 7.25/7.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.25/7.45         (((k2_relat_1 @ X1) != (X0))
% 7.25/7.45          | (zip_tseitin_0 @ X0 @ X2)
% 7.25/7.45          | ~ (v1_relat_1 @ X1)
% 7.25/7.45          | ~ (v1_funct_1 @ X1)
% 7.25/7.45          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 7.25/7.45          | ~ (v2_funct_1 @ X1))),
% 7.25/7.45      inference('sup-', [status(thm)], ['31', '37'])).
% 7.25/7.45  thf('39', plain,
% 7.25/7.45      (![X1 : $i, X2 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X1)
% 7.25/7.45          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 7.25/7.45          | ~ (v1_funct_1 @ X1)
% 7.25/7.45          | ~ (v1_relat_1 @ X1)
% 7.25/7.45          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 7.25/7.45      inference('simplify', [status(thm)], ['38'])).
% 7.25/7.45  thf('40', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((zip_tseitin_0 @ sk_B @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ sk_C_1)
% 7.25/7.45          | ~ (v1_funct_1 @ sk_C_1)
% 7.25/7.45          | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 7.25/7.45          | ~ (v2_funct_1 @ sk_C_1))),
% 7.25/7.45      inference('sup+', [status(thm)], ['30', '39'])).
% 7.25/7.45  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 7.25/7.45      inference('sup-', [status(thm)], ['2', '3'])).
% 7.25/7.45  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('43', plain, ((v2_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('44', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 7.25/7.45      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 7.25/7.45  thf('45', plain,
% 7.25/7.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.25/7.45  thf(zf_stmt_3, axiom,
% 7.25/7.45    (![C:$i,B:$i,A:$i]:
% 7.25/7.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.25/7.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.25/7.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 7.25/7.45  thf(zf_stmt_5, axiom,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.25/7.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.25/7.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.25/7.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.25/7.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.25/7.45  thf('46', plain,
% 7.25/7.45      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.25/7.45         (~ (zip_tseitin_0 @ X27 @ X28)
% 7.25/7.45          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 7.25/7.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.25/7.45  thf('47', plain,
% 7.25/7.45      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.25/7.45      inference('sup-', [status(thm)], ['45', '46'])).
% 7.25/7.45  thf('48', plain,
% 7.25/7.45      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 7.25/7.45        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 7.25/7.45      inference('sup-', [status(thm)], ['44', '47'])).
% 7.25/7.45  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('50', plain,
% 7.25/7.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.25/7.45         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 7.25/7.45          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 7.25/7.45          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.25/7.45  thf('51', plain,
% 7.25/7.45      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['49', '50'])).
% 7.25/7.45  thf('52', plain,
% 7.25/7.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf(redefinition_k1_relset_1, axiom,
% 7.25/7.45    (![A:$i,B:$i,C:$i]:
% 7.25/7.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.25/7.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.25/7.45  thf('53', plain,
% 7.25/7.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.25/7.45         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 7.25/7.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 7.25/7.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.25/7.45  thf('54', plain,
% 7.25/7.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 7.25/7.45      inference('sup-', [status(thm)], ['52', '53'])).
% 7.25/7.45  thf('55', plain,
% 7.25/7.45      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 7.25/7.45      inference('demod', [status(thm)], ['51', '54'])).
% 7.25/7.45  thf('56', plain,
% 7.25/7.45      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 7.25/7.45        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['48', '55'])).
% 7.25/7.45  thf('57', plain,
% 7.25/7.45      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf('58', plain,
% 7.25/7.45      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 7.25/7.45         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['56', '57'])).
% 7.25/7.45  thf('59', plain,
% 7.25/7.45      ((![X0 : $i]:
% 7.25/7.45          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['25', '58'])).
% 7.25/7.45  thf('60', plain,
% 7.25/7.45      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.25/7.45      inference('sup-', [status(thm)], ['45', '46'])).
% 7.25/7.45  thf('61', plain,
% 7.25/7.45      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 7.25/7.45         | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('sup-', [status(thm)], ['59', '60'])).
% 7.25/7.45  thf('62', plain,
% 7.25/7.45      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 7.25/7.45      inference('demod', [status(thm)], ['51', '54'])).
% 7.25/7.45  thf('63', plain,
% 7.25/7.45      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('clc', [status(thm)], ['61', '62'])).
% 7.25/7.45  thf('64', plain,
% 7.25/7.45      (![X12 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X12)
% 7.25/7.45          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 7.25/7.45          | ~ (v1_funct_1 @ X12)
% 7.25/7.45          | ~ (v1_relat_1 @ X12))),
% 7.25/7.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.25/7.45  thf('65', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf('66', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf('67', plain,
% 7.25/7.45      (![X12 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X12)
% 7.25/7.45          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 7.25/7.45          | ~ (v1_funct_1 @ X12)
% 7.25/7.45          | ~ (v1_relat_1 @ X12))),
% 7.25/7.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.25/7.45  thf(t3_funct_2, axiom,
% 7.25/7.45    (![A:$i]:
% 7.25/7.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.25/7.45       ( ( v1_funct_1 @ A ) & 
% 7.25/7.45         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 7.25/7.45         ( m1_subset_1 @
% 7.25/7.45           A @ 
% 7.25/7.45           ( k1_zfmisc_1 @
% 7.25/7.45             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 7.25/7.45  thf('68', plain,
% 7.25/7.45      (![X32 : $i]:
% 7.25/7.45         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 7.25/7.45          | ~ (v1_funct_1 @ X32)
% 7.25/7.45          | ~ (v1_relat_1 @ X32))),
% 7.25/7.45      inference('cnf', [status(esa)], [t3_funct_2])).
% 7.25/7.45  thf('69', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 7.25/7.45      inference('sup+', [status(thm)], ['67', '68'])).
% 7.25/7.45  thf('70', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['66', '69'])).
% 7.25/7.45  thf('71', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['70'])).
% 7.25/7.45  thf('72', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['65', '71'])).
% 7.25/7.45  thf('73', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['72'])).
% 7.25/7.45  thf('74', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45           (k1_relat_1 @ X0))
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0))),
% 7.25/7.45      inference('sup+', [status(thm)], ['64', '73'])).
% 7.25/7.45  thf('75', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 7.25/7.45             (k1_relat_1 @ X0)))),
% 7.25/7.45      inference('simplify', [status(thm)], ['74'])).
% 7.25/7.45  thf('76', plain,
% 7.25/7.45      ((((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 7.25/7.45         | ~ (v1_relat_1 @ sk_C_1)
% 7.25/7.45         | ~ (v1_funct_1 @ sk_C_1)
% 7.25/7.45         | ~ (v2_funct_1 @ sk_C_1)))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('sup+', [status(thm)], ['63', '75'])).
% 7.25/7.45  thf('77', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 7.25/7.45      inference('sup+', [status(thm)], ['28', '29'])).
% 7.25/7.45  thf('78', plain, ((v1_relat_1 @ sk_C_1)),
% 7.25/7.45      inference('sup-', [status(thm)], ['2', '3'])).
% 7.25/7.45  thf('79', plain, ((v1_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('80', plain, ((v2_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('81', plain,
% 7.25/7.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 7.25/7.45         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 7.25/7.45      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 7.25/7.45  thf('82', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 7.25/7.45      inference('demod', [status(thm)], ['11', '81'])).
% 7.25/7.45  thf('83', plain,
% 7.25/7.45      (~
% 7.25/7.45       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 7.25/7.45       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 7.25/7.45       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf('84', plain,
% 7.25/7.45      (~
% 7.25/7.45       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 7.25/7.45      inference('sat_resolution*', [status(thm)], ['10', '82', '83'])).
% 7.25/7.45  thf('85', plain,
% 7.25/7.45      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.25/7.45      inference('simpl_trail', [status(thm)], ['1', '84'])).
% 7.25/7.45  thf('86', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 7.25/7.45      inference('sup+', [status(thm)], ['28', '29'])).
% 7.25/7.45  thf('87', plain,
% 7.25/7.45      (![X12 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X12)
% 7.25/7.45          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 7.25/7.45          | ~ (v1_funct_1 @ X12)
% 7.25/7.45          | ~ (v1_relat_1 @ X12))),
% 7.25/7.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.25/7.45  thf('88', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf('89', plain,
% 7.25/7.45      (![X11 : $i]:
% 7.25/7.45         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 7.25/7.45          | ~ (v1_funct_1 @ X11)
% 7.25/7.45          | ~ (v1_relat_1 @ X11))),
% 7.25/7.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 7.25/7.45  thf('90', plain,
% 7.25/7.45      (![X12 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X12)
% 7.25/7.45          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 7.25/7.45          | ~ (v1_funct_1 @ X12)
% 7.25/7.45          | ~ (v1_relat_1 @ X12))),
% 7.25/7.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.25/7.45  thf('91', plain,
% 7.25/7.45      (![X32 : $i]:
% 7.25/7.45         ((m1_subset_1 @ X32 @ 
% 7.25/7.45           (k1_zfmisc_1 @ 
% 7.25/7.45            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 7.25/7.45          | ~ (v1_funct_1 @ X32)
% 7.25/7.45          | ~ (v1_relat_1 @ X32))),
% 7.25/7.45      inference('cnf', [status(esa)], [t3_funct_2])).
% 7.25/7.45  thf('92', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45           (k1_zfmisc_1 @ 
% 7.25/7.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 7.25/7.45      inference('sup+', [status(thm)], ['90', '91'])).
% 7.25/7.45  thf('93', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45             (k1_zfmisc_1 @ 
% 7.25/7.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 7.25/7.45               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['89', '92'])).
% 7.25/7.45  thf('94', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45           (k1_zfmisc_1 @ 
% 7.25/7.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['93'])).
% 7.25/7.45  thf('95', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45             (k1_zfmisc_1 @ 
% 7.25/7.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 7.25/7.45               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['88', '94'])).
% 7.25/7.45  thf('96', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45           (k1_zfmisc_1 @ 
% 7.25/7.45            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0))),
% 7.25/7.45      inference('simplify', [status(thm)], ['95'])).
% 7.25/7.45  thf('97', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v2_funct_1 @ X0))),
% 7.25/7.45      inference('sup+', [status(thm)], ['87', '96'])).
% 7.25/7.45  thf('98', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         (~ (v2_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_funct_1 @ X0)
% 7.25/7.45          | ~ (v1_relat_1 @ X0)
% 7.25/7.45          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 7.25/7.45             (k1_zfmisc_1 @ 
% 7.25/7.45              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 7.25/7.45      inference('simplify', [status(thm)], ['97'])).
% 7.25/7.45  thf('99', plain,
% 7.25/7.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 7.25/7.45        | ~ (v1_relat_1 @ sk_C_1)
% 7.25/7.45        | ~ (v1_funct_1 @ sk_C_1)
% 7.25/7.45        | ~ (v2_funct_1 @ sk_C_1))),
% 7.25/7.45      inference('sup+', [status(thm)], ['86', '98'])).
% 7.25/7.45  thf('100', plain,
% 7.25/7.45      (![X0 : $i]:
% 7.25/7.45         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 7.25/7.45      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 7.25/7.45  thf('101', plain,
% 7.25/7.45      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('split', [status(esa)], ['0'])).
% 7.25/7.45  thf('102', plain,
% 7.25/7.45      ((![X0 : $i]:
% 7.25/7.45          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 7.25/7.45              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 7.25/7.45           | (zip_tseitin_0 @ sk_B @ X0)))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['100', '101'])).
% 7.25/7.45  thf('103', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 7.25/7.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.25/7.45  thf('104', plain,
% 7.25/7.45      (![X7 : $i, X9 : $i]:
% 7.25/7.45         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 7.25/7.45      inference('cnf', [status(esa)], [t3_subset])).
% 7.25/7.45  thf('105', plain,
% 7.25/7.45      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 7.25/7.45      inference('sup-', [status(thm)], ['103', '104'])).
% 7.25/7.45  thf('106', plain,
% 7.25/7.45      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('demod', [status(thm)], ['102', '105'])).
% 7.25/7.45  thf('107', plain,
% 7.25/7.45      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.25/7.45      inference('sup-', [status(thm)], ['45', '46'])).
% 7.25/7.45  thf('108', plain,
% 7.25/7.45      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['106', '107'])).
% 7.25/7.45  thf('109', plain,
% 7.25/7.45      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 7.25/7.45        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 7.25/7.45      inference('demod', [status(thm)], ['51', '54'])).
% 7.25/7.45  thf('110', plain,
% 7.25/7.45      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 7.25/7.45         <= (~
% 7.25/7.45             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 7.25/7.45      inference('sup-', [status(thm)], ['108', '109'])).
% 7.25/7.45  thf('111', plain,
% 7.25/7.45      (~
% 7.25/7.45       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 7.25/7.45      inference('sat_resolution*', [status(thm)], ['10', '82', '83'])).
% 7.25/7.45  thf('112', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 7.25/7.45      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 7.25/7.45  thf('113', plain, ((v1_relat_1 @ sk_C_1)),
% 7.25/7.45      inference('sup-', [status(thm)], ['2', '3'])).
% 7.25/7.45  thf('114', plain, ((v1_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('115', plain, ((v2_funct_1 @ sk_C_1)),
% 7.25/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.45  thf('116', plain,
% 7.25/7.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 7.25/7.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.25/7.45      inference('demod', [status(thm)], ['99', '112', '113', '114', '115'])).
% 7.25/7.45  thf('117', plain, ($false), inference('demod', [status(thm)], ['85', '116'])).
% 7.25/7.45  
% 7.25/7.45  % SZS output end Refutation
% 7.25/7.45  
% 7.25/7.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
