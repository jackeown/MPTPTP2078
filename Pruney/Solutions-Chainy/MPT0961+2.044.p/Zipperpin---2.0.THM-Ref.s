%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hBxRGnLpkF

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (3086 expanded)
%              Number of leaves         :   27 ( 801 expanded)
%              Depth                    :   22
%              Number of atoms          :  975 (36138 expanded)
%              Number of equality atoms :   84 (1403 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ( X22 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('5',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X14 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['10','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','22'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('49',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','47','48'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('60',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('62',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['52','64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('68',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('77',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('78',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','71','75','76','77'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('81',plain,
    ( ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('88',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['73','74'])).

thf('91',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88','89','90'])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('93',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('96',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['65','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hBxRGnLpkF
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 107 iterations in 0.084s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(d1_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_1, axiom,
% 0.21/0.54    (![C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_3, axiom,
% 0.21/0.54    (![B:$i,A:$i]:
% 0.21/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.54  thf(zf_stmt_4, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (((X20) != (k1_xboole_0))
% 0.21/0.54          | ((X21) = (k1_xboole_0))
% 0.21/0.54          | (v1_funct_2 @ X22 @ X21 @ X20)
% 0.21/0.54          | ((X22) != (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X21 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ k1_xboole_0)))
% 0.21/0.54          | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)
% 0.21/0.54          | ((X21) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.54  thf(t113_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X21 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)
% 0.21/0.54          | ((X21) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((![X21 : $i]:
% 0.21/0.54          (((X21) = (k1_xboole_0))
% 0.21/0.54           | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf(t3_funct_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_funct_1 @ A ) & 
% 0.21/0.54         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @
% 0.21/0.54           A @ 
% 0.21/0.54           ( k1_zfmisc_1 @
% 0.21/0.54             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_5, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54          ( ( v1_funct_1 @ A ) & 
% 0.21/0.54            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54            ( m1_subset_1 @
% 0.21/0.54              A @ 
% 0.21/0.54              ( k1_zfmisc_1 @
% 0.21/0.54                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.21/0.54        | ~ (m1_subset_1 @ sk_A @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('9', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('10', plain, (((v1_funct_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.54  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.54  thf(t11_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.54           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ X14)
% 0.21/0.54          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.54          | ~ (v1_relat_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (m1_subset_1 @ X0 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ sk_A @ 
% 0.21/0.54           (k1_zfmisc_1 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m1_subset_1 @ sk_A @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_A))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m1_subset_1 @ sk_A @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_A @ 
% 0.21/0.54         (k1_zfmisc_1 @ 
% 0.21/0.54          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.21/0.54       ~
% 0.21/0.54       ((m1_subset_1 @ sk_A @ 
% 0.21/0.54         (k1_zfmisc_1 @ 
% 0.21/0.54          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.21/0.54       ~ ((v1_funct_1 @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['10', '20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['7', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.21/0.54          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.54              = (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (((X17) != (k1_relset_1 @ X17 @ X18 @ X19))
% 0.21/0.54          | (v1_funct_2 @ X19 @ X17 @ X18)
% 0.21/0.54          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.54          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['7', '22'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('40', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '40'])).
% 0.21/0.54  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf(t64_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X8 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['41', '47', '48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['41', '47', '48'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_A @ 
% 0.21/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.54  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('58', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.54  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('60', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.21/0.54         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((![X21 : $i]:
% 0.21/0.54          (((X21) = (k1_xboole_0))
% 0.21/0.54           | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))) | 
% 0.21/0.54       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((![X21 : $i]:
% 0.21/0.54          (((X21) = (k1_xboole_0))
% 0.21/0.54           | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['52', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((~ (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.21/0.54            k1_xboole_0)
% 0.21/0.54         | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54         | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.21/0.54            (k2_relat_1 @ k1_xboole_0))))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('71', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.54  thf(fc6_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.54  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.54  thf('77', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (((~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.54         | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '71', '75', '76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((~ (zip_tseitin_0 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.54         | (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.21/0.54            (k1_relat_1 @ k1_xboole_0))
% 0.21/0.54         | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.54  thf('82', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('85', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['84'])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.54      inference('sup+', [status(thm)], ['83', '85'])).
% 0.21/0.54  thf('87', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['86'])).
% 0.21/0.54  thf('88', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.54  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['81', '82', '87', '88', '89', '90'])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      ((![X21 : $i]:
% 0.21/0.54          (((X21) = (k1_xboole_0))
% 0.21/0.54           | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('93', plain, ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.54         <= ((![X21 : $i]:
% 0.21/0.54                (((X21) = (k1_xboole_0))
% 0.21/0.54                 | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['78', '93'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      ((![X21 : $i]:
% 0.21/0.54          (((X21) = (k1_xboole_0))
% 0.21/0.54           | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('96', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.21/0.54  thf('97', plain, ($false), inference('demod', [status(thm)], ['65', '96'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
