%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wPv3bGgecv

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 529 expanded)
%              Number of leaves         :   43 ( 176 expanded)
%              Depth                    :   21
%              Number of atoms          : 1660 (9184 expanded)
%              Number of equality atoms :  235 (1400 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X49
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k6_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k7_mcart_1 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X46 @ X47 @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X49
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k6_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k7_mcart_1 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('45',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('46',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','41','42','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['27','56'])).

thf('58',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X43 @ X42 )
      | ( ( sk_B @ X42 )
       != ( k3_mcart_1 @ X44 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','59'])).

thf('61',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50'])).

thf('63',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('64',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('66',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('67',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_mcart_1 @ X33 @ X34 @ X35 )
      = ( k4_tarski @ ( k4_tarski @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k2_mcart_1 @ X39 ) )
      | ( X39
       != ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('69',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_tarski @ X40 @ X41 )
     != ( k2_mcart_1 @ ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('70',plain,(
    ! [X54: $i,X56: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X54 @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_tarski @ X40 @ X41 )
     != X41 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('77',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('78',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('79',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('81',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ( ( sk_B @ X42 )
       != ( k3_mcart_1 @ X44 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('88',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X27 )
      | ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D_1 @ X0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( zip_tseitin_0 @ sk_D_1 @ X0 @ X1 @ X2 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['75','92'])).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('98',plain,
    ( sk_D_1
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['73','96','97'])).

thf('99',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 )
    | ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['61','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('101',plain,
    ( ( k1_tarski @ sk_D_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('103',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('105',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('106',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('109',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('110',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('112',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('113',plain,(
    ! [X26: $i,X27: $i] :
      ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('114',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('117',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
       != ( k2_tarski @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X1 @ X1 )
      | ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','119'])).

thf('121',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','122'])).

thf('124',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','123'])).

thf('125',plain,(
    $false ),
    inference(simplify,[status(thm)],['124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wPv3bGgecv
% 0.17/0.37  % Computer   : n012.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 18:21:52 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.49/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.66  % Solved by: fo/fo7.sh
% 0.49/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.66  % done 436 iterations in 0.180s
% 0.49/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.66  % SZS output start Refutation
% 0.49/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.66  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.49/0.66  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.49/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.66  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.49/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.66  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.49/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.49/0.66  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.49/0.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.49/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.66  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.49/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.49/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.66  thf(d1_enumset1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.49/0.66       ( ![E:$i]:
% 0.49/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.49/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.49/0.66  thf(zf_stmt_0, axiom,
% 0.49/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.49/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.49/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.49/0.66  thf('0', plain,
% 0.49/0.66      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.66         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.49/0.66          | ((X11) = (X12))
% 0.49/0.66          | ((X11) = (X13))
% 0.49/0.66          | ((X11) = (X14)))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(t29_mcart_1, axiom,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.49/0.66          ( ![B:$i]:
% 0.49/0.66            ( ~( ( r2_hidden @ B @ A ) & 
% 0.49/0.66                 ( ![C:$i,D:$i,E:$i]:
% 0.49/0.66                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.49/0.66                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.66  thf('1', plain,
% 0.49/0.66      (![X42 : $i]:
% 0.49/0.66         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.49/0.66      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.49/0.66  thf(t70_enumset1, axiom,
% 0.49/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.49/0.66  thf('2', plain,
% 0.49/0.66      (![X23 : $i, X24 : $i]:
% 0.49/0.66         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.49/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.49/0.66  thf(t69_enumset1, axiom,
% 0.49/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.66  thf('3', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.49/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.66  thf('4', plain,
% 0.49/0.66      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.49/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.49/0.66  thf(zf_stmt_2, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.49/0.66       ( ![E:$i]:
% 0.49/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.49/0.66  thf('5', plain,
% 0.49/0.66      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X20 @ X19)
% 0.49/0.66          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.49/0.66          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.66  thf('6', plain,
% 0.49/0.66      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.49/0.66         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.49/0.66          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.49/0.66      inference('simplify', [status(thm)], ['5'])).
% 0.49/0.66  thf('7', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.49/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['4', '6'])).
% 0.49/0.66  thf('8', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.66          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['1', '7'])).
% 0.49/0.66  thf('9', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.49/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.49/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.49/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['0', '8'])).
% 0.49/0.66  thf('10', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.49/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.49/0.66  thf('11', plain,
% 0.49/0.66      (![X42 : $i]:
% 0.49/0.66         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.49/0.66      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.49/0.66  thf('12', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.49/0.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.67          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.67          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.49/0.67  thf(t51_mcart_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ~( ![D:$i]:
% 0.49/0.67               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.49/0.67                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.49/0.67                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.49/0.67                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_3, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.67        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67             ( ~( ![D:$i]:
% 0.49/0.67                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.49/0.67                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.49/0.67                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.49/0.67                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf(d3_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.49/0.67       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.67         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.49/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.67        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf(t50_mcart_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ~( ![D:$i]:
% 0.49/0.67               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.49/0.67                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.49/0.67                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.49/0.67                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.49/0.67                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.49/0.67                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k6_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.49/0.67              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.67         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.49/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k6_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.49/0.67              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ 
% 0.49/0.67               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      ((((sk_C) = (k1_xboole_0))
% 0.49/0.67        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.49/0.67        | ((sk_B_1) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['16', '19'])).
% 0.49/0.67  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('22', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.49/0.67        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.49/0.67        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('split', [status(esa)], ['25'])).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['24', '26'])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.67        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf(t48_mcart_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.49/0.67          ( ~( ![D:$i]:
% 0.49/0.67               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.49/0.67                 ( ( D ) =
% 0.49/0.67                   ( k3_mcart_1 @
% 0.49/0.67                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.49/0.67                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.49/0.67                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.49/0.67         (((X46) = (k1_xboole_0))
% 0.49/0.67          | ((X47) = (k1_xboole_0))
% 0.49/0.67          | ((X49)
% 0.49/0.67              = (k3_mcart_1 @ (k5_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.49/0.67                 (k6_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.49/0.67                 (k7_mcart_1 @ X46 @ X47 @ X48 @ X49)))
% 0.49/0.67          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X46 @ X47 @ X48))
% 0.49/0.67          | ((X48) = (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.67         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.49/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.49/0.67         (((X46) = (k1_xboole_0))
% 0.49/0.67          | ((X47) = (k1_xboole_0))
% 0.49/0.67          | ((X49)
% 0.49/0.67              = (k3_mcart_1 @ (k5_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.49/0.67                 (k6_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.49/0.67                 (k7_mcart_1 @ X46 @ X47 @ X48 @ X49)))
% 0.49/0.67          | ~ (m1_subset_1 @ X49 @ 
% 0.49/0.67               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X48))
% 0.49/0.67          | ((X48) = (k1_xboole_0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      ((((sk_C) = (k1_xboole_0))
% 0.49/0.67        | ((sk_D_1)
% 0.49/0.67            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.49/0.67               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.49/0.67               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.49/0.67        | ((sk_B_1) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['28', '31'])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.67        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k5_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.49/0.67              = (k1_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.67         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.49/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k5_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.49/0.67              = (k1_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ 
% 0.49/0.67               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      ((((sk_C) = (k1_xboole_0))
% 0.49/0.67        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.49/0.67        | ((sk_B_1) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['33', '36'])).
% 0.49/0.67  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('39', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['37', '38', '39', '40'])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.67        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k7_mcart_1 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.49/0.67  thf('45', plain,
% 0.49/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.67         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.49/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.67  thf('46', plain,
% 0.49/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.49/0.67         (((X50) = (k1_xboole_0))
% 0.49/0.67          | ((X51) = (k1_xboole_0))
% 0.49/0.67          | ((k7_mcart_1 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 0.49/0.67          | ~ (m1_subset_1 @ X52 @ 
% 0.49/0.67               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.49/0.67          | ((X53) = (k1_xboole_0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['44', '45'])).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      ((((sk_C) = (k1_xboole_0))
% 0.49/0.67        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))
% 0.49/0.67        | ((sk_B_1) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['43', '46'])).
% 0.49/0.67  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['47', '48', '49', '50'])).
% 0.49/0.67  thf('52', plain,
% 0.49/0.67      ((((sk_C) = (k1_xboole_0))
% 0.49/0.67        | ((sk_D_1)
% 0.49/0.67            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.49/0.67        | ((sk_B_1) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['32', '41', '42', '51'])).
% 0.49/0.67  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('54', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('56', plain,
% 0.49/0.67      (((sk_D_1)
% 0.49/0.67         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.49/0.67  thf('57', plain,
% 0.49/0.67      ((((sk_D_1)
% 0.49/0.67          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1 @ 
% 0.49/0.67             (k2_mcart_1 @ sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['27', '56'])).
% 0.49/0.67  thf('58', plain,
% 0.49/0.67      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.49/0.67         (((X42) = (k1_xboole_0))
% 0.49/0.67          | ~ (r2_hidden @ X43 @ X42)
% 0.49/0.67          | ((sk_B @ X42) != (k3_mcart_1 @ X44 @ X43 @ X45)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.49/0.67  thf('59', plain,
% 0.49/0.67      ((![X0 : $i]:
% 0.49/0.67          (((sk_B @ X0) != (sk_D_1))
% 0.49/0.67           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.49/0.67           | ((X0) = (k1_xboole_0))))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.67  thf('60', plain,
% 0.49/0.67      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.49/0.67         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.49/0.67         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['13', '59'])).
% 0.49/0.67  thf('61', plain,
% 0.49/0.67      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.49/0.67         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.49/0.67         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['60'])).
% 0.49/0.67  thf('62', plain,
% 0.49/0.67      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['47', '48', '49', '50'])).
% 0.49/0.67  thf('63', plain,
% 0.49/0.67      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.49/0.67         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('split', [status(esa)], ['25'])).
% 0.49/0.67  thf('64', plain,
% 0.49/0.67      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.49/0.67         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['62', '63'])).
% 0.49/0.67  thf('65', plain,
% 0.49/0.67      (((sk_D_1)
% 0.49/0.67         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.49/0.67  thf('66', plain,
% 0.49/0.67      ((((sk_D_1)
% 0.49/0.67          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.49/0.67         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['64', '65'])).
% 0.49/0.67  thf(d3_mcart_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.49/0.67  thf('67', plain,
% 0.49/0.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.67         ((k3_mcart_1 @ X33 @ X34 @ X35)
% 0.49/0.67           = (k4_tarski @ (k4_tarski @ X33 @ X34) @ X35))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.49/0.67  thf(t20_mcart_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.49/0.67       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.49/0.67  thf('68', plain,
% 0.49/0.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.49/0.67         (((X39) != (k2_mcart_1 @ X39)) | ((X39) != (k4_tarski @ X40 @ X41)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.49/0.67  thf('69', plain,
% 0.49/0.67      (![X40 : $i, X41 : $i]:
% 0.49/0.67         ((k4_tarski @ X40 @ X41) != (k2_mcart_1 @ (k4_tarski @ X40 @ X41)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['68'])).
% 0.49/0.67  thf(t7_mcart_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.49/0.67       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.49/0.67  thf('70', plain,
% 0.49/0.67      (![X54 : $i, X56 : $i]: ((k2_mcart_1 @ (k4_tarski @ X54 @ X56)) = (X56))),
% 0.49/0.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.49/0.67  thf('71', plain, (![X40 : $i, X41 : $i]: ((k4_tarski @ X40 @ X41) != (X41))),
% 0.49/0.67      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.67  thf('72', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['67', '71'])).
% 0.49/0.67  thf('73', plain,
% 0.49/0.67      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['66', '72'])).
% 0.49/0.67  thf('74', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.67         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.49/0.67          | (r2_hidden @ X15 @ X19)
% 0.49/0.67          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.67  thf('75', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.67         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.49/0.67          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.49/0.67      inference('simplify', [status(thm)], ['74'])).
% 0.49/0.67  thf('76', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.67          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.49/0.67  thf('77', plain,
% 0.49/0.67      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.49/0.67         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['37', '38', '39', '40'])).
% 0.49/0.67  thf('78', plain,
% 0.49/0.67      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('split', [status(esa)], ['25'])).
% 0.49/0.67  thf('79', plain,
% 0.49/0.67      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['77', '78'])).
% 0.49/0.67  thf('80', plain,
% 0.49/0.67      (((sk_D_1)
% 0.49/0.67         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.49/0.67  thf('81', plain,
% 0.49/0.67      ((((sk_D_1)
% 0.49/0.67          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.49/0.67             (k2_mcart_1 @ sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['79', '80'])).
% 0.49/0.67  thf('82', plain,
% 0.49/0.67      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.49/0.67         (((X42) = (k1_xboole_0))
% 0.49/0.67          | ~ (r2_hidden @ X44 @ X42)
% 0.49/0.67          | ((sk_B @ X42) != (k3_mcart_1 @ X44 @ X43 @ X45)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.49/0.67  thf('83', plain,
% 0.49/0.67      ((![X0 : $i]:
% 0.49/0.67          (((sk_B @ X0) != (sk_D_1))
% 0.49/0.67           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.49/0.67           | ((X0) = (k1_xboole_0))))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.67  thf('84', plain,
% 0.49/0.67      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.49/0.67         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.49/0.67         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['76', '83'])).
% 0.49/0.67  thf('85', plain,
% 0.49/0.67      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.49/0.67         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['84'])).
% 0.49/0.67  thf('86', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.67          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.49/0.67  thf('87', plain,
% 0.49/0.67      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('clc', [status(thm)], ['85', '86'])).
% 0.49/0.67  thf(t64_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.49/0.67       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.49/0.67  thf('88', plain,
% 0.49/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.67         (((X25) != (X27))
% 0.49/0.67          | ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27))))),
% 0.49/0.67      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.49/0.67  thf('89', plain,
% 0.49/0.67      (![X26 : $i, X27 : $i]:
% 0.49/0.67         ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['88'])).
% 0.49/0.67  thf('90', plain,
% 0.49/0.67      ((![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['87', '89'])).
% 0.49/0.67  thf(t3_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.67  thf('91', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.67  thf('92', plain,
% 0.49/0.67      ((![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ X0))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.67  thf('93', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i, X2 : $i]: (zip_tseitin_0 @ sk_D_1 @ X0 @ X1 @ X2))
% 0.49/0.67         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['75', '92'])).
% 0.49/0.67  thf('94', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.67         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('95', plain,
% 0.49/0.67      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.49/0.67         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.49/0.67      inference('simplify', [status(thm)], ['94'])).
% 0.49/0.67  thf('96', plain,
% 0.49/0.67      (~ (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['93', '95'])).
% 0.49/0.67  thf('97', plain,
% 0.49/0.67      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.49/0.67       (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.49/0.67       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.49/0.67      inference('split', [status(esa)], ['25'])).
% 0.49/0.67  thf('98', plain,
% 0.49/0.67      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.49/0.67      inference('sat_resolution*', [status(thm)], ['73', '96', '97'])).
% 0.49/0.67  thf('99', plain,
% 0.49/0.67      ((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.49/0.67        | ((k1_tarski @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.67      inference('simpl_trail', [status(thm)], ['61', '98'])).
% 0.49/0.67  thf('100', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.67          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.49/0.67  thf('101', plain, (((k1_tarski @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.67      inference('clc', [status(thm)], ['99', '100'])).
% 0.49/0.67  thf('102', plain,
% 0.49/0.67      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.49/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.67  thf('103', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.67         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.49/0.67          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.49/0.67      inference('simplify', [status(thm)], ['74'])).
% 0.49/0.67  thf('104', plain,
% 0.49/0.67      (![X23 : $i, X24 : $i]:
% 0.49/0.67         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.49/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.49/0.67  thf('105', plain,
% 0.49/0.67      (![X42 : $i]:
% 0.49/0.67         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.49/0.67      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.49/0.67  thf('106', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.67  thf(t48_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('107', plain,
% 0.49/0.67      (![X7 : $i, X8 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.49/0.67           = (k3_xboole_0 @ X7 @ X8))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('108', plain,
% 0.49/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['106', '107'])).
% 0.49/0.67  thf(d4_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.49/0.67       ( ![D:$i]:
% 0.49/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.49/0.67  thf('109', plain,
% 0.49/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X4 @ X3)
% 0.49/0.67          | (r2_hidden @ X4 @ X2)
% 0.49/0.67          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.49/0.67  thf('110', plain,
% 0.49/0.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.49/0.67         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['109'])).
% 0.49/0.67  thf('111', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.49/0.67          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['108', '110'])).
% 0.49/0.67  thf(t4_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.67  thf('112', plain,
% 0.49/0.67      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.67  thf('113', plain,
% 0.49/0.67      (![X26 : $i, X27 : $i]:
% 0.49/0.67         ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['88'])).
% 0.49/0.67  thf('114', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.67      inference('sup-', [status(thm)], ['112', '113'])).
% 0.49/0.67  thf('115', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.49/0.67      inference('clc', [status(thm)], ['111', '114'])).
% 0.49/0.67  thf('116', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['105', '115'])).
% 0.49/0.67  thf(t72_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.49/0.67       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.49/0.67  thf('117', plain,
% 0.49/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X29 @ X30)
% 0.49/0.67          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30)
% 0.49/0.67              != (k2_tarski @ X29 @ X31)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.49/0.67  thf('118', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.49/0.67          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['116', '117'])).
% 0.49/0.67  thf('119', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.49/0.67          | ((k1_xboole_0) != (k2_tarski @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['104', '118'])).
% 0.49/0.67  thf('120', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((zip_tseitin_0 @ X1 @ X0 @ X1 @ X1)
% 0.49/0.67          | ((k1_xboole_0) != (k2_tarski @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['103', '119'])).
% 0.49/0.67  thf('121', plain,
% 0.49/0.67      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.49/0.67         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.49/0.67      inference('simplify', [status(thm)], ['94'])).
% 0.49/0.67  thf('122', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.49/0.67      inference('clc', [status(thm)], ['120', '121'])).
% 0.49/0.67  thf('123', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['102', '122'])).
% 0.49/0.67  thf('124', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['101', '123'])).
% 0.49/0.67  thf('125', plain, ($false), inference('simplify', [status(thm)], ['124'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
