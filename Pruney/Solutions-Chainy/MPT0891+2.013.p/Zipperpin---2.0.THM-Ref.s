%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QIiLkyMY1w

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 550 expanded)
%              Number of leaves         :   42 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          : 1661 (9197 expanded)
%              Number of equality atoms :  251 (1421 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
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
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

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

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X43 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('35',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X42
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ ( k6_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ ( k7_mcart_1 @ X39 @ X40 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k3_zfmisc_1 @ X39 @ X40 @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X42
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ ( k6_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ ( k7_mcart_1 @ X39 @ X40 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X43 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k2_mcart_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X43 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('51',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('52',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X43 @ X44 @ X46 @ X45 )
        = ( k2_mcart_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','48','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X35 )
      | ( ( sk_B @ X35 )
       != ( k3_mcart_1 @ X37 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
          = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_D ) )
          = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','66'])).

thf('68',plain,
    ( ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( ( k1_tarski @ sk_D )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['53','54','55','56'])).

thf('77',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('78',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59','60','61'])).

thf('80',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('81',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
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

thf('82',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k2_mcart_1 @ X32 ) )
      | ( X32
       != ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('83',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k4_tarski @ X33 @ X34 )
     != ( k2_mcart_1 @ ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('84',plain,(
    ! [X47: $i,X49: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X47 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k4_tarski @ X33 @ X34 )
     != X34 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('90',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45','46','47'])).

thf('91',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('92',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59','60','61'])).

thf('94',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ( ( sk_B @ X35 )
       != ( k3_mcart_1 @ X37 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
          = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_D ) )
          = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf('99',plain,
    ( ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('101',plain,
    ( ( ( ( k1_tarski @ sk_D )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('105',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X22 @ X24 ) @ X23 )
       != ( k2_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X1 @ X1 )
      | ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('119',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['87','117','118'])).

thf('120',plain,
    ( ( k1_tarski @ sk_D )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('122',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(simplify,[status(thm)],['122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QIiLkyMY1w
% 0.17/0.38  % Computer   : n014.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 18:45:22 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 328 iterations in 0.138s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.63  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.63  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.63  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.46/0.63  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.46/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.63  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.63  thf(d1_enumset1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.63       ( ![E:$i]:
% 0.46/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, axiom,
% 0.46/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.46/0.63          | ((X5) = (X6))
% 0.46/0.63          | ((X5) = (X7))
% 0.46/0.63          | ((X5) = (X8)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t29_mcart_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.63                 ( ![C:$i,D:$i,E:$i]:
% 0.46/0.63                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.63                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X35 : $i]:
% 0.46/0.63         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.63  thf(t70_enumset1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.63  thf(t69_enumset1, axiom,
% 0.46/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.63  thf('3', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.63       ( ![E:$i]:
% 0.46/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X14 @ X13)
% 0.46/0.63          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.46/0.63          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.46/0.63         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.46/0.63          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '7'])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.63          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.63  thf(t65_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.46/0.63       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]:
% 0.46/0.63         (((k4_xboole_0 @ X20 @ (k1_tarski @ X21)) = (X20))
% 0.46/0.63          | (r2_hidden @ X21 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.63  thf(t48_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.46/0.63           = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.46/0.63          | (r2_hidden @ X1 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf(t3_boole, axiom,
% 0.46/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.63  thf('14', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.46/0.63           = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf(t2_boole, axiom,
% 0.46/0.63    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.63  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['13', '18'])).
% 0.46/0.63  thf(t51_mcart_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ~( ![D:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.63                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.63                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.63                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_3, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.63        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63             ( ~( ![D:$i]:
% 0.46/0.63                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.63                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.63                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.63                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf(d3_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.46/0.63       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.63         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.46/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ 
% 0.46/0.63        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf(t50_mcart_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ~( ![D:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.63                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.46/0.63                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.46/0.63                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.46/0.63                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.46/0.63                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k5_mcart_1 @ X43 @ X44 @ X46 @ X45)
% 0.46/0.63              = (k1_mcart_1 @ (k1_mcart_1 @ X45)))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X43 @ X44 @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.63         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.46/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k5_mcart_1 @ X43 @ X44 @ X46 @ X45)
% 0.46/0.63              = (k1_mcart_1 @ (k1_mcart_1 @ X45)))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ 
% 0.46/0.63               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0))
% 0.46/0.63        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.46/0.63        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.46/0.63  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.46/0.63        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.46/0.63        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('split', [status(esa)], ['31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      ((((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['30', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ 
% 0.46/0.63        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf(t48_mcart_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ~( ![D:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.63                 ( ( D ) =
% 0.46/0.63                   ( k3_mcart_1 @
% 0.46/0.63                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.46/0.63                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.46/0.63                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.63         (((X39) = (k1_xboole_0))
% 0.46/0.63          | ((X40) = (k1_xboole_0))
% 0.46/0.63          | ((X42)
% 0.46/0.63              = (k3_mcart_1 @ (k5_mcart_1 @ X39 @ X40 @ X41 @ X42) @ 
% 0.46/0.63                 (k6_mcart_1 @ X39 @ X40 @ X41 @ X42) @ 
% 0.46/0.63                 (k7_mcart_1 @ X39 @ X40 @ X41 @ X42)))
% 0.46/0.63          | ~ (m1_subset_1 @ X42 @ (k3_zfmisc_1 @ X39 @ X40 @ X41))
% 0.46/0.63          | ((X41) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.63         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.46/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.63         (((X39) = (k1_xboole_0))
% 0.46/0.63          | ((X40) = (k1_xboole_0))
% 0.46/0.63          | ((X42)
% 0.46/0.63              = (k3_mcart_1 @ (k5_mcart_1 @ X39 @ X40 @ X41 @ X42) @ 
% 0.46/0.63                 (k6_mcart_1 @ X39 @ X40 @ X41 @ X42) @ 
% 0.46/0.63                 (k7_mcart_1 @ X39 @ X40 @ X41 @ X42)))
% 0.46/0.63          | ~ (m1_subset_1 @ X42 @ 
% 0.46/0.63               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40) @ X41))
% 0.46/0.63          | ((X41) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0))
% 0.46/0.63        | ((sk_D)
% 0.46/0.63            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.46/0.63               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.46/0.63               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.46/0.63        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ 
% 0.46/0.63        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k6_mcart_1 @ X43 @ X44 @ X46 @ X45)
% 0.46/0.63              = (k2_mcart_1 @ (k1_mcart_1 @ X45)))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X43 @ X44 @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.63         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.46/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k6_mcart_1 @ X43 @ X44 @ X46 @ X45)
% 0.46/0.63              = (k2_mcart_1 @ (k1_mcart_1 @ X45)))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ 
% 0.46/0.63               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0))
% 0.46/0.63        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.46/0.63        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.63  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('47', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['44', '45', '46', '47'])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ 
% 0.46/0.63        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k7_mcart_1 @ X43 @ X44 @ X46 @ X45) = (k2_mcart_1 @ X45))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X43 @ X44 @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.63         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.46/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.46/0.63         (((X43) = (k1_xboole_0))
% 0.46/0.63          | ((X44) = (k1_xboole_0))
% 0.46/0.63          | ((k7_mcart_1 @ X43 @ X44 @ X46 @ X45) = (k2_mcart_1 @ X45))
% 0.46/0.63          | ~ (m1_subset_1 @ X45 @ 
% 0.46/0.63               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X46))
% 0.46/0.63          | ((X46) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0))
% 0.46/0.63        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.46/0.63        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '52'])).
% 0.46/0.63  thf('54', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('55', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('56', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['53', '54', '55', '56'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      ((((sk_C) = (k1_xboole_0))
% 0.46/0.63        | ((sk_D)
% 0.46/0.63            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.46/0.63               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.46/0.63        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['38', '39', '48', '57'])).
% 0.46/0.63  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('60', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('61', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (((sk_D)
% 0.46/0.63         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.46/0.63            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['58', '59', '60', '61'])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.63         (((X35) = (k1_xboole_0))
% 0.46/0.63          | ~ (r2_hidden @ X37 @ X35)
% 0.46/0.63          | ((sk_B @ X35) != (k3_mcart_1 @ X37 @ X36 @ X38)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_B @ X0) != (sk_D))
% 0.46/0.63          | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ X0)
% 0.46/0.63          | ((X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (r2_hidden @ sk_D @ X0)
% 0.46/0.63           | ((X0) = (k1_xboole_0))
% 0.46/0.63           | ((sk_B @ X0) != (sk_D))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['33', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (((k3_xboole_0 @ X0 @ (k1_tarski @ sk_D)) = (k1_xboole_0))
% 0.46/0.63           | ((sk_B @ X0) != (sk_D))
% 0.46/0.63           | ((X0) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['19', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (((X0) != (sk_D))
% 0.46/0.63           | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63           | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63           | ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_D))
% 0.46/0.63               = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '66'])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (((((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D))
% 0.46/0.63           = (k1_xboole_0))
% 0.46/0.63         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.63  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.46/0.63           = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.63  thf('72', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.63  thf('73', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      (((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.46/0.63         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('demod', [status(thm)], ['68', '73'])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.46/0.63         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['53', '54', '55', '56'])).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.46/0.63         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('split', [status(esa)], ['31'])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.46/0.63         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (((sk_D)
% 0.46/0.63         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.46/0.63            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['58', '59', '60', '61'])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      ((((sk_D)
% 0.46/0.63          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.46/0.63             (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ sk_D)))
% 0.46/0.63         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['78', '79'])).
% 0.46/0.63  thf(d3_mcart_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.63         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 0.46/0.63           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.46/0.63  thf(t20_mcart_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.63       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.63         (((X32) != (k2_mcart_1 @ X32)) | ((X32) != (k4_tarski @ X33 @ X34)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (![X33 : $i, X34 : $i]:
% 0.46/0.63         ((k4_tarski @ X33 @ X34) != (k2_mcart_1 @ (k4_tarski @ X33 @ X34)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.46/0.63  thf(t7_mcart_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.46/0.63       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (![X47 : $i, X49 : $i]: ((k2_mcart_1 @ (k4_tarski @ X47 @ X49)) = (X49))),
% 0.46/0.63      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.63  thf('85', plain, (![X33 : $i, X34 : $i]: ((k4_tarski @ X33 @ X34) != (X34))),
% 0.46/0.63      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['81', '85'])).
% 0.46/0.63  thf('87', plain, (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['80', '86'])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['13', '18'])).
% 0.46/0.63  thf('90', plain,
% 0.46/0.63      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.63         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['44', '45', '46', '47'])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('split', [status(esa)], ['31'])).
% 0.46/0.63  thf('92', plain,
% 0.46/0.63      ((((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['90', '91'])).
% 0.46/0.63  thf('93', plain,
% 0.46/0.63      (((sk_D)
% 0.46/0.63         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.46/0.63            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['58', '59', '60', '61'])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.63         (((X35) = (k1_xboole_0))
% 0.46/0.63          | ~ (r2_hidden @ X36 @ X35)
% 0.46/0.63          | ((sk_B @ X35) != (k3_mcart_1 @ X37 @ X36 @ X38)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.63  thf('95', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_B @ X0) != (sk_D))
% 0.46/0.63          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ X0)
% 0.46/0.63          | ((X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.63  thf('96', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (r2_hidden @ sk_D @ X0)
% 0.46/0.63           | ((X0) = (k1_xboole_0))
% 0.46/0.63           | ((sk_B @ X0) != (sk_D))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['92', '95'])).
% 0.46/0.63  thf('97', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (((k3_xboole_0 @ X0 @ (k1_tarski @ sk_D)) = (k1_xboole_0))
% 0.46/0.63           | ((sk_B @ X0) != (sk_D))
% 0.46/0.63           | ((X0) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['89', '96'])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (((X0) != (sk_D))
% 0.46/0.63           | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63           | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.63           | ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_D))
% 0.46/0.63               = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['88', '97'])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      (((((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D))
% 0.46/0.63           = (k1_xboole_0))
% 0.46/0.63         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.63  thf('100', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.63  thf('101', plain,
% 0.46/0.63      (((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.46/0.63         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('demod', [status(thm)], ['99', '100'])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['101'])).
% 0.46/0.63  thf('103', plain,
% 0.46/0.63      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.63  thf('104', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.46/0.63          | (r2_hidden @ X9 @ X13)
% 0.46/0.63          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.63  thf('105', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.63         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.46/0.63          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.46/0.63      inference('simplify', [status(thm)], ['104'])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.63  thf('107', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf(t72_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.63       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.46/0.63  thf('108', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X22 @ X23)
% 0.46/0.63          | ((k4_xboole_0 @ (k2_tarski @ X22 @ X24) @ X23)
% 0.46/0.63              != (k2_tarski @ X22 @ X24)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.46/0.63  thf('109', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.46/0.63          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.63  thf('110', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.46/0.63          | ((k1_xboole_0) != (k2_tarski @ X1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['106', '109'])).
% 0.46/0.63  thf('111', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X1 @ X0 @ X1 @ X1)
% 0.46/0.63          | ((k1_xboole_0) != (k2_tarski @ X1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['105', '110'])).
% 0.46/0.63  thf('112', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.63         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('113', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.46/0.63      inference('simplify', [status(thm)], ['112'])).
% 0.46/0.63  thf('114', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['111', '113'])).
% 0.46/0.63  thf('115', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['103', '114'])).
% 0.46/0.63  thf('116', plain,
% 0.46/0.63      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.63         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['102', '115'])).
% 0.46/0.63  thf('117', plain,
% 0.46/0.63      (~ (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['116'])).
% 0.46/0.63  thf('118', plain,
% 0.46/0.63      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.46/0.63       (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.46/0.63       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.46/0.63      inference('split', [status(esa)], ['31'])).
% 0.46/0.63  thf('119', plain, ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['87', '117', '118'])).
% 0.46/0.63  thf('120', plain, (((k1_tarski @ sk_D) = (k1_xboole_0))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['75', '119'])).
% 0.46/0.63  thf('121', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['103', '114'])).
% 0.46/0.63  thf('122', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.63  thf('123', plain, ($false), inference('simplify', [status(thm)], ['122'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
