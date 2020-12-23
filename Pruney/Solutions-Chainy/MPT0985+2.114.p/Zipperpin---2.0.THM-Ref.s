%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Te33O2RuEC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:42 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 538 expanded)
%              Number of leaves         :   43 ( 175 expanded)
%              Depth                    :   25
%              Number of atoms          : 1471 (8401 expanded)
%              Number of equality atoms :   79 ( 343 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('19',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,
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

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('39',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('58',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('60',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['57','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','79'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','80'])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','81','82'])).

thf('84',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','83'])).

thf('85',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('86',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('87',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('91',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('93',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('101',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('102',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('103',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('106',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('108',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','81','82'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['85','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['84','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Te33O2RuEC
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:23:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.33/3.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.33/3.54  % Solved by: fo/fo7.sh
% 3.33/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.54  % done 3804 iterations in 3.083s
% 3.33/3.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.33/3.54  % SZS output start Refutation
% 3.33/3.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.33/3.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.33/3.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.33/3.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.33/3.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.33/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.33/3.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.33/3.54  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 3.33/3.54  thf(sk_C_type, type, sk_C: $i).
% 3.33/3.54  thf(sk_B_type, type, sk_B: $i).
% 3.33/3.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.33/3.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.33/3.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.33/3.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.33/3.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.33/3.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.33/3.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.33/3.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.33/3.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.33/3.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.33/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.33/3.54  thf(t31_funct_2, conjecture,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.54       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.33/3.54         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.33/3.54           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.33/3.54           ( m1_subset_1 @
% 3.33/3.54             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.33/3.54  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.54    (~( ![A:$i,B:$i,C:$i]:
% 3.33/3.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.54          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.33/3.54            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.33/3.54              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.33/3.54              ( m1_subset_1 @
% 3.33/3.54                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.33/3.54    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.33/3.54  thf('0', plain,
% 3.33/3.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.33/3.54        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('1', plain,
% 3.33/3.54      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('2', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(cc1_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( v1_relat_1 @ C ) ))).
% 3.33/3.54  thf('3', plain,
% 3.33/3.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.33/3.54         ((v1_relat_1 @ X13)
% 3.33/3.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.33/3.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.33/3.54  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf(dt_k2_funct_1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.33/3.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.33/3.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.33/3.54  thf('5', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf('6', plain,
% 3.33/3.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.33/3.54         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('7', plain,
% 3.33/3.54      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 3.33/3.54         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['5', '6'])).
% 3.33/3.54  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('9', plain,
% 3.33/3.54      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.33/3.54      inference('demod', [status(thm)], ['7', '8'])).
% 3.33/3.54  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['4', '9'])).
% 3.33/3.54  thf('11', plain,
% 3.33/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('12', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(redefinition_k2_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.33/3.54  thf('13', plain,
% 3.33/3.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.33/3.54         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 3.33/3.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.33/3.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.33/3.54  thf('14', plain,
% 3.33/3.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.33/3.54      inference('sup-', [status(thm)], ['12', '13'])).
% 3.33/3.54  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.33/3.54      inference('sup+', [status(thm)], ['14', '15'])).
% 3.33/3.54  thf(d1_funct_2, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.33/3.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.33/3.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.33/3.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.33/3.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.33/3.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.33/3.54  thf(zf_stmt_1, axiom,
% 3.33/3.54    (![B:$i,A:$i]:
% 3.33/3.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.33/3.54       ( zip_tseitin_0 @ B @ A ) ))).
% 3.33/3.54  thf('17', plain,
% 3.33/3.54      (![X22 : $i, X23 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.54  thf('18', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf(t55_funct_1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.33/3.54       ( ( v2_funct_1 @ A ) =>
% 3.33/3.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.33/3.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.33/3.54  thf('19', plain,
% 3.33/3.54      (![X11 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X11)
% 3.33/3.54          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 3.33/3.54          | ~ (v1_funct_1 @ X11)
% 3.33/3.54          | ~ (v1_relat_1 @ X11))),
% 3.33/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.33/3.54  thf(t64_relat_1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( v1_relat_1 @ A ) =>
% 3.33/3.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.33/3.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.33/3.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.33/3.54  thf('20', plain,
% 3.33/3.54      (![X9 : $i]:
% 3.33/3.54         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 3.33/3.54          | ((X9) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_relat_1 @ X9))),
% 3.33/3.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.33/3.54  thf('21', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['19', '20'])).
% 3.33/3.54  thf('22', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['18', '21'])).
% 3.33/3.54  thf('23', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['22'])).
% 3.33/3.54  thf('24', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.54         (((k2_relat_1 @ X1) != (X0))
% 3.33/3.54          | (zip_tseitin_0 @ X0 @ X2)
% 3.33/3.54          | ~ (v1_relat_1 @ X1)
% 3.33/3.54          | ~ (v1_funct_1 @ X1)
% 3.33/3.54          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.33/3.54          | ~ (v2_funct_1 @ X1))),
% 3.33/3.54      inference('sup-', [status(thm)], ['17', '23'])).
% 3.33/3.54  thf('25', plain,
% 3.33/3.54      (![X1 : $i, X2 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X1)
% 3.33/3.54          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.33/3.54          | ~ (v1_funct_1 @ X1)
% 3.33/3.54          | ~ (v1_relat_1 @ X1)
% 3.33/3.54          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 3.33/3.54      inference('simplify', [status(thm)], ['24'])).
% 3.33/3.54  thf('26', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ sk_B @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ sk_C)
% 3.33/3.54          | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 3.33/3.54          | ~ (v2_funct_1 @ sk_C))),
% 3.33/3.54      inference('sup+', [status(thm)], ['16', '25'])).
% 3.33/3.54  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('30', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.33/3.54  thf('31', plain,
% 3.33/3.54      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('32', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 3.33/3.54           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['30', '31'])).
% 3.33/3.54  thf('33', plain,
% 3.33/3.54      (![X22 : $i, X23 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.54  thf(t60_relat_1, axiom,
% 3.33/3.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.33/3.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.33/3.54  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.33/3.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.33/3.54  thf(t4_funct_2, axiom,
% 3.33/3.54    (![A:$i,B:$i]:
% 3.33/3.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.33/3.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.33/3.54         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.33/3.54           ( m1_subset_1 @
% 3.33/3.54             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.33/3.54  thf('35', plain,
% 3.33/3.54      (![X30 : $i, X31 : $i]:
% 3.33/3.54         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 3.33/3.54          | (v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ X31)
% 3.33/3.54          | ~ (v1_funct_1 @ X30)
% 3.33/3.54          | ~ (v1_relat_1 @ X30))),
% 3.33/3.54      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.33/3.54  thf('36', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.33/3.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 3.33/3.54          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.33/3.54      inference('sup-', [status(thm)], ['34', '35'])).
% 3.33/3.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.33/3.54  thf('37', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.33/3.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.33/3.54  thf(t45_ordinal1, axiom,
% 3.33/3.54    (![A:$i]:
% 3.33/3.54     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 3.33/3.54       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 3.33/3.54  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.33/3.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 3.33/3.54  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 3.33/3.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 3.33/3.54  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.33/3.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.33/3.54  thf('41', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.33/3.54      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 3.33/3.54  thf('42', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.54         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.33/3.54      inference('sup+', [status(thm)], ['33', '41'])).
% 3.33/3.54  thf('43', plain,
% 3.33/3.54      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('clc', [status(thm)], ['32', '42'])).
% 3.33/3.54  thf('44', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.33/3.54  thf(zf_stmt_3, axiom,
% 3.33/3.54    (![C:$i,B:$i,A:$i]:
% 3.33/3.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.33/3.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.33/3.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.33/3.54  thf(zf_stmt_5, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.33/3.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.33/3.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.33/3.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.33/3.54  thf('45', plain,
% 3.33/3.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.33/3.54         (~ (zip_tseitin_0 @ X27 @ X28)
% 3.33/3.54          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 3.33/3.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.33/3.54  thf('46', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['44', '45'])).
% 3.33/3.54  thf('47', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['43', '46'])).
% 3.33/3.54  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('49', plain,
% 3.33/3.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.33/3.54         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 3.33/3.54          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 3.33/3.54          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.33/3.54  thf('50', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 3.33/3.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['48', '49'])).
% 3.33/3.54  thf('51', plain,
% 3.33/3.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf(redefinition_k1_relset_1, axiom,
% 3.33/3.54    (![A:$i,B:$i,C:$i]:
% 3.33/3.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.33/3.54  thf('52', plain,
% 3.33/3.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.33/3.54         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.33/3.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.33/3.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.33/3.54  thf('53', plain,
% 3.33/3.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.33/3.54      inference('sup-', [status(thm)], ['51', '52'])).
% 3.33/3.54  thf('54', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.33/3.54      inference('demod', [status(thm)], ['50', '53'])).
% 3.33/3.54  thf('55', plain,
% 3.33/3.54      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['47', '54'])).
% 3.33/3.54  thf('56', plain,
% 3.33/3.54      (![X11 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X11)
% 3.33/3.54          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 3.33/3.54          | ~ (v1_funct_1 @ X11)
% 3.33/3.54          | ~ (v1_relat_1 @ X11))),
% 3.33/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.33/3.54  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.33/3.54      inference('sup+', [status(thm)], ['14', '15'])).
% 3.33/3.54  thf('58', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf('59', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf('60', plain,
% 3.33/3.54      (![X11 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X11)
% 3.33/3.54          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 3.33/3.54          | ~ (v1_funct_1 @ X11)
% 3.33/3.54          | ~ (v1_relat_1 @ X11))),
% 3.33/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.33/3.54  thf(d10_xboole_0, axiom,
% 3.33/3.54    (![A:$i,B:$i]:
% 3.33/3.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.33/3.54  thf('61', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.33/3.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.33/3.54  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.33/3.54      inference('simplify', [status(thm)], ['61'])).
% 3.33/3.54  thf('63', plain,
% 3.33/3.54      (![X30 : $i, X31 : $i]:
% 3.33/3.54         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 3.33/3.54          | (v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ X31)
% 3.33/3.54          | ~ (v1_funct_1 @ X30)
% 3.33/3.54          | ~ (v1_relat_1 @ X30))),
% 3.33/3.54      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.33/3.54  thf('64', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['62', '63'])).
% 3.33/3.54  thf('65', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.33/3.54           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.33/3.54      inference('sup+', [status(thm)], ['60', '64'])).
% 3.33/3.54  thf('66', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.33/3.54             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['59', '65'])).
% 3.33/3.54  thf('67', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.33/3.54           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['66'])).
% 3.33/3.54  thf('68', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.33/3.54             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['58', '67'])).
% 3.33/3.54  thf('69', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.33/3.54           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ X0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['68'])).
% 3.33/3.54  thf('70', plain,
% 3.33/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.33/3.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.33/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.33/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.33/3.54      inference('sup+', [status(thm)], ['57', '69'])).
% 3.33/3.54  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('74', plain,
% 3.33/3.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 3.33/3.54        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.33/3.54      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 3.33/3.54  thf('75', plain,
% 3.33/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 3.33/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.33/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.33/3.54      inference('sup+', [status(thm)], ['56', '74'])).
% 3.33/3.54  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('79', plain,
% 3.33/3.54      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 3.33/3.54      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 3.33/3.54  thf('80', plain,
% 3.33/3.54      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.33/3.54         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.33/3.54      inference('sup+', [status(thm)], ['55', '79'])).
% 3.33/3.54  thf('81', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.33/3.54      inference('demod', [status(thm)], ['11', '80'])).
% 3.33/3.54  thf('82', plain,
% 3.33/3.54      (~
% 3.33/3.54       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 3.33/3.54       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 3.33/3.54       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('83', plain,
% 3.33/3.54      (~
% 3.33/3.54       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.33/3.54      inference('sat_resolution*', [status(thm)], ['10', '81', '82'])).
% 3.33/3.54  thf('84', plain,
% 3.33/3.54      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.54      inference('simpl_trail', [status(thm)], ['1', '83'])).
% 3.33/3.54  thf('85', plain,
% 3.33/3.54      (![X11 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X11)
% 3.33/3.54          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 3.33/3.54          | ~ (v1_funct_1 @ X11)
% 3.33/3.54          | ~ (v1_relat_1 @ X11))),
% 3.33/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.33/3.54  thf('86', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.33/3.54      inference('simplify', [status(thm)], ['61'])).
% 3.33/3.54  thf('87', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf('88', plain,
% 3.33/3.54      (![X10 : $i]:
% 3.33/3.54         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.33/3.54          | ~ (v1_funct_1 @ X10)
% 3.33/3.54          | ~ (v1_relat_1 @ X10))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.33/3.54  thf('89', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.33/3.54      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.33/3.54  thf('90', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['44', '45'])).
% 3.33/3.54  thf('91', plain,
% 3.33/3.54      ((((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 3.33/3.54        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['89', '90'])).
% 3.33/3.54  thf('92', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.33/3.54      inference('demod', [status(thm)], ['50', '53'])).
% 3.33/3.54  thf('93', plain,
% 3.33/3.54      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['91', '92'])).
% 3.33/3.54  thf('94', plain,
% 3.33/3.54      (![X22 : $i, X23 : $i]:
% 3.33/3.54         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.54  thf(t113_zfmisc_1, axiom,
% 3.33/3.54    (![A:$i,B:$i]:
% 3.33/3.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.33/3.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.33/3.54  thf('95', plain,
% 3.33/3.54      (![X5 : $i, X6 : $i]:
% 3.33/3.54         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 3.33/3.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.33/3.54  thf('96', plain,
% 3.33/3.54      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.33/3.54      inference('simplify', [status(thm)], ['95'])).
% 3.33/3.54  thf('97', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.54         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.33/3.54      inference('sup+', [status(thm)], ['94', '96'])).
% 3.33/3.54  thf('98', plain,
% 3.33/3.54      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('split', [status(esa)], ['0'])).
% 3.33/3.54  thf('99', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.33/3.54           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['97', '98'])).
% 3.33/3.54  thf('100', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.33/3.54           | ((sk_A) = (k1_relat_1 @ sk_C))
% 3.33/3.54           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['93', '99'])).
% 3.33/3.54  thf(dt_k2_subset_1, axiom,
% 3.33/3.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.33/3.54  thf('101', plain,
% 3.33/3.54      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 3.33/3.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.33/3.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.33/3.54  thf('102', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 3.33/3.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.33/3.54  thf('103', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.33/3.54      inference('demod', [status(thm)], ['101', '102'])).
% 3.33/3.54  thf('104', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ sk_B @ X0)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('demod', [status(thm)], ['100', '103'])).
% 3.33/3.54  thf('105', plain,
% 3.33/3.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.33/3.54      inference('sup-', [status(thm)], ['44', '45'])).
% 3.33/3.54  thf('106', plain,
% 3.33/3.54      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['104', '105'])).
% 3.33/3.54  thf('107', plain,
% 3.33/3.54      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.33/3.54      inference('demod', [status(thm)], ['50', '53'])).
% 3.33/3.54  thf('108', plain,
% 3.33/3.54      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('clc', [status(thm)], ['106', '107'])).
% 3.33/3.54  thf('109', plain,
% 3.33/3.54      (![X11 : $i]:
% 3.33/3.54         (~ (v2_funct_1 @ X11)
% 3.33/3.54          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 3.33/3.54          | ~ (v1_funct_1 @ X11)
% 3.33/3.54          | ~ (v1_relat_1 @ X11))),
% 3.33/3.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.33/3.54  thf('110', plain,
% 3.33/3.54      (![X30 : $i, X31 : $i]:
% 3.33/3.54         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 3.33/3.54          | (m1_subset_1 @ X30 @ 
% 3.33/3.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ X31)))
% 3.33/3.54          | ~ (v1_funct_1 @ X30)
% 3.33/3.54          | ~ (v1_relat_1 @ X30))),
% 3.33/3.54      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.33/3.54  thf('111', plain,
% 3.33/3.54      (![X0 : $i, X1 : $i]:
% 3.33/3.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.33/3.54          | ~ (v1_relat_1 @ X0)
% 3.33/3.54          | ~ (v1_funct_1 @ X0)
% 3.33/3.54          | ~ (v2_funct_1 @ X0)
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['109', '110'])).
% 3.33/3.54  thf('112', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (~ (r1_tarski @ sk_A @ X0)
% 3.33/3.54           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54              (k1_zfmisc_1 @ 
% 3.33/3.54               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.33/3.54           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54           | ~ (v2_funct_1 @ sk_C)
% 3.33/3.54           | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54           | ~ (v1_relat_1 @ sk_C)))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['108', '111'])).
% 3.33/3.54  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('116', plain,
% 3.33/3.54      ((![X0 : $i]:
% 3.33/3.54          (~ (r1_tarski @ sk_A @ X0)
% 3.33/3.54           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54              (k1_zfmisc_1 @ 
% 3.33/3.54               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.33/3.54           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 3.33/3.54         <= (~
% 3.33/3.54             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.33/3.54      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 3.33/3.54  thf('117', plain,
% 3.33/3.54      (~
% 3.33/3.54       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.33/3.54      inference('sat_resolution*', [status(thm)], ['10', '81', '82'])).
% 3.33/3.54  thf('118', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (r1_tarski @ sk_A @ X0)
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.33/3.54          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.33/3.54      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 3.33/3.54  thf('119', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ sk_C)
% 3.33/3.54          | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.33/3.54          | ~ (r1_tarski @ sk_A @ X0))),
% 3.33/3.54      inference('sup-', [status(thm)], ['88', '118'])).
% 3.33/3.54  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('122', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.33/3.54          | ~ (r1_tarski @ sk_A @ X0))),
% 3.33/3.54      inference('demod', [status(thm)], ['119', '120', '121'])).
% 3.33/3.54  thf('123', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (v1_relat_1 @ sk_C)
% 3.33/3.54          | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54          | ~ (r1_tarski @ sk_A @ X0)
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.33/3.54      inference('sup-', [status(thm)], ['87', '122'])).
% 3.33/3.54  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('126', plain,
% 3.33/3.54      (![X0 : $i]:
% 3.33/3.54         (~ (r1_tarski @ sk_A @ X0)
% 3.33/3.54          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54             (k1_zfmisc_1 @ 
% 3.33/3.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.33/3.54      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.33/3.54  thf('127', plain,
% 3.33/3.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54        (k1_zfmisc_1 @ 
% 3.33/3.54         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 3.33/3.54      inference('sup-', [status(thm)], ['86', '126'])).
% 3.33/3.54  thf('128', plain,
% 3.33/3.54      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 3.33/3.54        | ~ (v1_relat_1 @ sk_C)
% 3.33/3.54        | ~ (v1_funct_1 @ sk_C)
% 3.33/3.54        | ~ (v2_funct_1 @ sk_C))),
% 3.33/3.54      inference('sup+', [status(thm)], ['85', '127'])).
% 3.33/3.54  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.33/3.54      inference('sup+', [status(thm)], ['14', '15'])).
% 3.33/3.54  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 3.33/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.54  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 3.33/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.54  thf('133', plain,
% 3.33/3.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.33/3.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.54      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 3.33/3.54  thf('134', plain, ($false), inference('demod', [status(thm)], ['84', '133'])).
% 3.33/3.54  
% 3.33/3.54  % SZS output end Refutation
% 3.33/3.54  
% 3.33/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
