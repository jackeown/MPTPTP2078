%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zEC0f95koy

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:45 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 491 expanded)
%              Number of leaves         :   40 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          : 1431 (7579 expanded)
%              Number of equality atoms :   79 ( 328 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C_1 )
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X29: $i] :
      ( ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','74','75'])).

thf('77',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('80',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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

thf('89',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['79','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('91',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('97',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('99',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('101',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['100','102'])).

thf('104',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('108',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('109',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('111',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('112',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('113',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('114',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','114'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('117',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('119',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','74','75'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('123',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','121','122','123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['77','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zEC0f95koy
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.49/1.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.72  % Solved by: fo/fo7.sh
% 1.49/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.72  % done 1636 iterations in 1.255s
% 1.49/1.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.72  % SZS output start Refutation
% 1.49/1.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.49/1.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.49/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.49/1.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.49/1.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.49/1.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.49/1.72  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 1.49/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.49/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.49/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.49/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.49/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.49/1.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.49/1.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.49/1.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.49/1.72  thf(t31_funct_2, conjecture,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.49/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.49/1.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.49/1.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.49/1.72           ( m1_subset_1 @
% 1.49/1.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.49/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.72    (~( ![A:$i,B:$i,C:$i]:
% 1.49/1.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.49/1.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.72          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.49/1.72            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.49/1.72              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.49/1.72              ( m1_subset_1 @
% 1.49/1.72                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.49/1.72    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.49/1.72  thf('0', plain,
% 1.49/1.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.49/1.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 1.49/1.72        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('1', plain,
% 1.49/1.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('2', plain,
% 1.49/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf(cc1_relset_1, axiom,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.72       ( v1_relat_1 @ C ) ))).
% 1.49/1.72  thf('3', plain,
% 1.49/1.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.49/1.72         ((v1_relat_1 @ X12)
% 1.49/1.72          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.49/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.49/1.72  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 1.49/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.72  thf(dt_k2_funct_1, axiom,
% 1.49/1.72    (![A:$i]:
% 1.49/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.49/1.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.49/1.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.49/1.72  thf('5', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf('6', plain,
% 1.49/1.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.49/1.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('7', plain,
% 1.49/1.72      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 1.49/1.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['5', '6'])).
% 1.49/1.72  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('9', plain,
% 1.49/1.72      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.49/1.72      inference('demod', [status(thm)], ['7', '8'])).
% 1.49/1.72  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['4', '9'])).
% 1.49/1.72  thf('11', plain,
% 1.49/1.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('12', plain,
% 1.49/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf(redefinition_k2_relset_1, axiom,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.49/1.72  thf('13', plain,
% 1.49/1.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.49/1.72         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.49/1.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.49/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.49/1.72  thf('14', plain,
% 1.49/1.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.49/1.72      inference('sup-', [status(thm)], ['12', '13'])).
% 1.49/1.72  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('16', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 1.49/1.72      inference('sup+', [status(thm)], ['14', '15'])).
% 1.49/1.72  thf(d1_funct_2, axiom,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.49/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.49/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.49/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.49/1.72  thf(zf_stmt_1, axiom,
% 1.49/1.72    (![B:$i,A:$i]:
% 1.49/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.49/1.72  thf('17', plain,
% 1.49/1.72      (![X21 : $i, X22 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.72  thf('18', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf(t55_funct_1, axiom,
% 1.49/1.72    (![A:$i]:
% 1.49/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.49/1.72       ( ( v2_funct_1 @ A ) =>
% 1.49/1.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.49/1.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.49/1.72  thf('19', plain,
% 1.49/1.72      (![X10 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X10)
% 1.49/1.72          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.49/1.72          | ~ (v1_funct_1 @ X10)
% 1.49/1.72          | ~ (v1_relat_1 @ X10))),
% 1.49/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.49/1.72  thf(t64_relat_1, axiom,
% 1.49/1.72    (![A:$i]:
% 1.49/1.72     ( ( v1_relat_1 @ A ) =>
% 1.49/1.72       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.49/1.72           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.72         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.49/1.72  thf('20', plain,
% 1.49/1.72      (![X8 : $i]:
% 1.49/1.72         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 1.49/1.72          | ((X8) = (k1_xboole_0))
% 1.49/1.72          | ~ (v1_relat_1 @ X8))),
% 1.49/1.72      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.49/1.72  thf('21', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['19', '20'])).
% 1.49/1.72  thf('22', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['18', '21'])).
% 1.49/1.72  thf('23', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['22'])).
% 1.49/1.72  thf('24', plain,
% 1.49/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.72         (((k2_relat_1 @ X1) != (X0))
% 1.49/1.72          | (zip_tseitin_0 @ X0 @ X2)
% 1.49/1.72          | ~ (v1_relat_1 @ X1)
% 1.49/1.72          | ~ (v1_funct_1 @ X1)
% 1.49/1.72          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.49/1.72          | ~ (v2_funct_1 @ X1))),
% 1.49/1.72      inference('sup-', [status(thm)], ['17', '23'])).
% 1.49/1.72  thf('25', plain,
% 1.49/1.72      (![X1 : $i, X2 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X1)
% 1.49/1.72          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.49/1.72          | ~ (v1_funct_1 @ X1)
% 1.49/1.72          | ~ (v1_relat_1 @ X1)
% 1.49/1.72          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 1.49/1.72      inference('simplify', [status(thm)], ['24'])).
% 1.49/1.72  thf('26', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ sk_B @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ sk_C_1)
% 1.49/1.72          | ~ (v1_funct_1 @ sk_C_1)
% 1.49/1.72          | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 1.49/1.72          | ~ (v2_funct_1 @ sk_C_1))),
% 1.49/1.72      inference('sup+', [status(thm)], ['16', '25'])).
% 1.49/1.72  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 1.49/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.72  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('29', plain, ((v2_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('30', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.49/1.72      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.49/1.72  thf('31', plain,
% 1.49/1.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('32', plain,
% 1.49/1.72      ((![X0 : $i]:
% 1.49/1.72          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 1.49/1.72           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['30', '31'])).
% 1.49/1.72  thf('33', plain,
% 1.49/1.72      (![X21 : $i, X22 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.72  thf(t60_relat_1, axiom,
% 1.49/1.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.49/1.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.49/1.72  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.49/1.72  thf(t4_funct_2, axiom,
% 1.49/1.72    (![A:$i,B:$i]:
% 1.49/1.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.49/1.72       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.49/1.72         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.49/1.72           ( m1_subset_1 @
% 1.49/1.72             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.49/1.72  thf('35', plain,
% 1.49/1.72      (![X30 : $i, X31 : $i]:
% 1.49/1.72         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 1.49/1.72          | (v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ X31)
% 1.49/1.72          | ~ (v1_funct_1 @ X30)
% 1.49/1.72          | ~ (v1_relat_1 @ X30))),
% 1.49/1.72      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.49/1.72  thf('36', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.72          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.49/1.72          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.49/1.72      inference('sup-', [status(thm)], ['34', '35'])).
% 1.49/1.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.49/1.72  thf('37', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.49/1.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.49/1.72  thf(t45_ordinal1, axiom,
% 1.49/1.72    (![A:$i]:
% 1.49/1.72     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 1.49/1.72       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 1.49/1.72  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.49/1.72  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.49/1.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.49/1.72  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.49/1.72  thf('41', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.49/1.72      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 1.49/1.72  thf('42', plain,
% 1.49/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.72         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.49/1.72      inference('sup+', [status(thm)], ['33', '41'])).
% 1.49/1.72  thf('43', plain,
% 1.49/1.72      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('clc', [status(thm)], ['32', '42'])).
% 1.49/1.72  thf('44', plain,
% 1.49/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.49/1.72  thf(zf_stmt_3, axiom,
% 1.49/1.72    (![C:$i,B:$i,A:$i]:
% 1.49/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.49/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.49/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.49/1.72  thf(zf_stmt_5, axiom,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.49/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.49/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.49/1.72  thf('45', plain,
% 1.49/1.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.49/1.72         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.49/1.72          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.49/1.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.49/1.72  thf('46', plain,
% 1.49/1.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.49/1.72      inference('sup-', [status(thm)], ['44', '45'])).
% 1.49/1.72  thf('47', plain,
% 1.49/1.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['43', '46'])).
% 1.49/1.72  thf('48', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('49', plain,
% 1.49/1.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.49/1.72         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.49/1.72          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.49/1.72          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.49/1.72  thf('50', plain,
% 1.49/1.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['48', '49'])).
% 1.49/1.72  thf('51', plain,
% 1.49/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.49/1.72    (![A:$i,B:$i,C:$i]:
% 1.49/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.49/1.72  thf('52', plain,
% 1.49/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.49/1.72         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 1.49/1.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.49/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.49/1.72  thf('53', plain,
% 1.49/1.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.49/1.72      inference('sup-', [status(thm)], ['51', '52'])).
% 1.49/1.72  thf('54', plain,
% 1.49/1.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.49/1.72      inference('demod', [status(thm)], ['50', '53'])).
% 1.49/1.72  thf('55', plain,
% 1.49/1.72      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['47', '54'])).
% 1.49/1.72  thf('56', plain,
% 1.49/1.72      (![X10 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X10)
% 1.49/1.72          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.49/1.72          | ~ (v1_funct_1 @ X10)
% 1.49/1.72          | ~ (v1_relat_1 @ X10))),
% 1.49/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.49/1.72  thf('57', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf('58', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf('59', plain,
% 1.49/1.72      (![X10 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X10)
% 1.49/1.72          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.49/1.72          | ~ (v1_funct_1 @ X10)
% 1.49/1.72          | ~ (v1_relat_1 @ X10))),
% 1.49/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.49/1.72  thf(t3_funct_2, axiom,
% 1.49/1.72    (![A:$i]:
% 1.49/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.49/1.72       ( ( v1_funct_1 @ A ) & 
% 1.49/1.72         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.49/1.72         ( m1_subset_1 @
% 1.49/1.72           A @ 
% 1.49/1.72           ( k1_zfmisc_1 @
% 1.49/1.72             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.49/1.72  thf('60', plain,
% 1.49/1.72      (![X29 : $i]:
% 1.49/1.72         ((v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))
% 1.49/1.72          | ~ (v1_funct_1 @ X29)
% 1.49/1.72          | ~ (v1_relat_1 @ X29))),
% 1.49/1.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.49/1.72  thf('61', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.49/1.72      inference('sup+', [status(thm)], ['59', '60'])).
% 1.49/1.72  thf('62', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['58', '61'])).
% 1.49/1.72  thf('63', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['62'])).
% 1.49/1.72  thf('64', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['57', '63'])).
% 1.49/1.72  thf('65', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['64'])).
% 1.49/1.72  thf('66', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72           (k1_relat_1 @ X0))
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0))),
% 1.49/1.72      inference('sup+', [status(thm)], ['56', '65'])).
% 1.49/1.72  thf('67', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.49/1.72             (k1_relat_1 @ X0)))),
% 1.49/1.72      inference('simplify', [status(thm)], ['66'])).
% 1.49/1.72  thf('68', plain,
% 1.49/1.72      ((((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 1.49/1.72         | ~ (v1_relat_1 @ sk_C_1)
% 1.49/1.72         | ~ (v1_funct_1 @ sk_C_1)
% 1.49/1.72         | ~ (v2_funct_1 @ sk_C_1)))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('sup+', [status(thm)], ['55', '67'])).
% 1.49/1.72  thf('69', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 1.49/1.72      inference('sup+', [status(thm)], ['14', '15'])).
% 1.49/1.72  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 1.49/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.72  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('72', plain, ((v2_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('73', plain,
% 1.49/1.72      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.49/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.49/1.72      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.49/1.72  thf('74', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 1.49/1.72      inference('demod', [status(thm)], ['11', '73'])).
% 1.49/1.72  thf('75', plain,
% 1.49/1.72      (~
% 1.49/1.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.49/1.72       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 1.49/1.72       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('76', plain,
% 1.49/1.72      (~
% 1.49/1.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.49/1.72      inference('sat_resolution*', [status(thm)], ['10', '74', '75'])).
% 1.49/1.72  thf('77', plain,
% 1.49/1.72      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.49/1.72      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 1.49/1.72  thf('78', plain,
% 1.49/1.72      (![X10 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X10)
% 1.49/1.72          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.49/1.72          | ~ (v1_funct_1 @ X10)
% 1.49/1.72          | ~ (v1_relat_1 @ X10))),
% 1.49/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.49/1.72  thf('79', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 1.49/1.72      inference('sup+', [status(thm)], ['14', '15'])).
% 1.49/1.72  thf('80', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf('81', plain,
% 1.49/1.72      (![X9 : $i]:
% 1.49/1.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.49/1.72          | ~ (v1_funct_1 @ X9)
% 1.49/1.72          | ~ (v1_relat_1 @ X9))),
% 1.49/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.49/1.72  thf('82', plain,
% 1.49/1.72      (![X10 : $i]:
% 1.49/1.72         (~ (v2_funct_1 @ X10)
% 1.49/1.72          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.49/1.72          | ~ (v1_funct_1 @ X10)
% 1.49/1.72          | ~ (v1_relat_1 @ X10))),
% 1.49/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.49/1.72  thf('83', plain,
% 1.49/1.72      (![X29 : $i]:
% 1.49/1.72         ((m1_subset_1 @ X29 @ 
% 1.49/1.72           (k1_zfmisc_1 @ 
% 1.49/1.72            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))))
% 1.49/1.72          | ~ (v1_funct_1 @ X29)
% 1.49/1.72          | ~ (v1_relat_1 @ X29))),
% 1.49/1.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.49/1.72  thf('84', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.49/1.72           (k1_zfmisc_1 @ 
% 1.49/1.72            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.49/1.72      inference('sup+', [status(thm)], ['82', '83'])).
% 1.49/1.72  thf('85', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.49/1.72             (k1_zfmisc_1 @ 
% 1.49/1.72              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.49/1.72               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['81', '84'])).
% 1.49/1.72  thf('86', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.49/1.72           (k1_zfmisc_1 @ 
% 1.49/1.72            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['85'])).
% 1.49/1.72  thf('87', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         (~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.49/1.72             (k1_zfmisc_1 @ 
% 1.49/1.72              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.49/1.72               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['80', '86'])).
% 1.49/1.72  thf('88', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.49/1.72           (k1_zfmisc_1 @ 
% 1.49/1.72            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.49/1.72          | ~ (v2_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_funct_1 @ X0)
% 1.49/1.72          | ~ (v1_relat_1 @ X0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['87'])).
% 1.49/1.72  thf('89', plain,
% 1.49/1.72      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72         (k1_zfmisc_1 @ 
% 1.49/1.72          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 1.49/1.72        | ~ (v1_relat_1 @ sk_C_1)
% 1.49/1.72        | ~ (v1_funct_1 @ sk_C_1)
% 1.49/1.72        | ~ (v2_funct_1 @ sk_C_1))),
% 1.49/1.72      inference('sup+', [status(thm)], ['79', '88'])).
% 1.49/1.72  thf('90', plain, ((v1_relat_1 @ sk_C_1)),
% 1.49/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.72  thf('91', plain, ((v1_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('92', plain, ((v2_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('93', plain,
% 1.49/1.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72        (k1_zfmisc_1 @ 
% 1.49/1.72         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 1.49/1.72      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 1.49/1.72  thf('94', plain,
% 1.49/1.72      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 1.49/1.72        | ~ (v1_relat_1 @ sk_C_1)
% 1.49/1.72        | ~ (v1_funct_1 @ sk_C_1)
% 1.49/1.72        | ~ (v2_funct_1 @ sk_C_1))),
% 1.49/1.72      inference('sup+', [status(thm)], ['78', '93'])).
% 1.49/1.72  thf('95', plain,
% 1.49/1.72      (![X0 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.49/1.72      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.49/1.72  thf('96', plain,
% 1.49/1.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.49/1.72      inference('sup-', [status(thm)], ['44', '45'])).
% 1.49/1.72  thf('97', plain,
% 1.49/1.72      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 1.49/1.72        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.49/1.72      inference('sup-', [status(thm)], ['95', '96'])).
% 1.49/1.72  thf('98', plain,
% 1.49/1.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.49/1.72      inference('demod', [status(thm)], ['50', '53'])).
% 1.49/1.72  thf('99', plain,
% 1.49/1.72      ((((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 1.49/1.72        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.49/1.72      inference('sup-', [status(thm)], ['97', '98'])).
% 1.49/1.72  thf('100', plain,
% 1.49/1.72      (![X21 : $i, X22 : $i]:
% 1.49/1.72         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.49/1.72  thf(t113_zfmisc_1, axiom,
% 1.49/1.72    (![A:$i,B:$i]:
% 1.49/1.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.49/1.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.49/1.72  thf('101', plain,
% 1.49/1.72      (![X6 : $i, X7 : $i]:
% 1.49/1.72         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.49/1.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.49/1.72  thf('102', plain,
% 1.49/1.72      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['101'])).
% 1.49/1.72  thf('103', plain,
% 1.49/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.72         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.49/1.72      inference('sup+', [status(thm)], ['100', '102'])).
% 1.49/1.72  thf('104', plain,
% 1.49/1.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('split', [status(esa)], ['0'])).
% 1.49/1.72  thf('105', plain,
% 1.49/1.72      ((![X0 : $i]:
% 1.49/1.72          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.49/1.72           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['103', '104'])).
% 1.49/1.72  thf('106', plain,
% 1.49/1.72      ((![X0 : $i]:
% 1.49/1.72          (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.49/1.72           | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.49/1.72           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['99', '105'])).
% 1.49/1.72  thf('107', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.49/1.72  thf('108', plain,
% 1.49/1.72      (![X29 : $i]:
% 1.49/1.72         ((m1_subset_1 @ X29 @ 
% 1.49/1.72           (k1_zfmisc_1 @ 
% 1.49/1.72            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))))
% 1.49/1.72          | ~ (v1_funct_1 @ X29)
% 1.49/1.72          | ~ (v1_relat_1 @ X29))),
% 1.49/1.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.49/1.72  thf('109', plain,
% 1.49/1.72      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.49/1.72         (k1_zfmisc_1 @ 
% 1.49/1.72          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))
% 1.49/1.72        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.72        | ~ (v1_funct_1 @ k1_xboole_0))),
% 1.49/1.72      inference('sup+', [status(thm)], ['107', '108'])).
% 1.49/1.72  thf('110', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.49/1.72  thf('111', plain,
% 1.49/1.72      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.49/1.72      inference('simplify', [status(thm)], ['101'])).
% 1.49/1.72  thf('112', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.49/1.72  thf('113', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.49/1.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.49/1.72  thf('114', plain,
% 1.49/1.72      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.49/1.72      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.49/1.72  thf('115', plain,
% 1.49/1.72      ((![X0 : $i]:
% 1.49/1.72          (((sk_A) = (k1_relat_1 @ sk_C_1)) | (zip_tseitin_0 @ sk_B @ X0)))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('demod', [status(thm)], ['106', '114'])).
% 1.49/1.72  thf('116', plain,
% 1.49/1.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.49/1.72      inference('sup-', [status(thm)], ['44', '45'])).
% 1.49/1.72  thf('117', plain,
% 1.49/1.72      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.49/1.72         | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('sup-', [status(thm)], ['115', '116'])).
% 1.49/1.72  thf('118', plain,
% 1.49/1.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.49/1.72        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.49/1.72      inference('demod', [status(thm)], ['50', '53'])).
% 1.49/1.72  thf('119', plain,
% 1.49/1.72      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 1.49/1.72         <= (~
% 1.49/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.49/1.72      inference('clc', [status(thm)], ['117', '118'])).
% 1.49/1.72  thf('120', plain,
% 1.49/1.72      (~
% 1.49/1.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.49/1.72      inference('sat_resolution*', [status(thm)], ['10', '74', '75'])).
% 1.49/1.72  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.49/1.72      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 1.49/1.72  thf('122', plain, ((v1_relat_1 @ sk_C_1)),
% 1.49/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.72  thf('123', plain, ((v1_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('124', plain, ((v2_funct_1 @ sk_C_1)),
% 1.49/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.72  thf('125', plain,
% 1.49/1.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.49/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.49/1.72      inference('demod', [status(thm)], ['94', '121', '122', '123', '124'])).
% 1.49/1.72  thf('126', plain, ($false), inference('demod', [status(thm)], ['77', '125'])).
% 1.49/1.72  
% 1.49/1.72  % SZS output end Refutation
% 1.49/1.72  
% 1.49/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
