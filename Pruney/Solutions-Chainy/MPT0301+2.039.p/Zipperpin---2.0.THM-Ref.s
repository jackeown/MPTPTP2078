%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LRvuQleJzj

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 15.91s
% Output     : Refutation 15.91s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 194 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  723 (1766 expanded)
%              Number of equality atoms :  107 ( 299 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t113_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
      <=> ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X19 @ X15 @ X16 ) @ ( sk_E @ X19 @ X15 @ X16 ) @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('14',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('22',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','37'])).

thf('39',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('44',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X18 @ X15 @ X16 ) @ ( sk_E_1 @ X18 @ X15 @ X16 ) @ X18 @ X15 @ X16 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X18 @ X15 @ X16 ) @ ( sk_E_1 @ X18 @ X15 @ X16 ) @ X18 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X6 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('55',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('60',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('62',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','45','46','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LRvuQleJzj
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:28:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 15.91/16.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.91/16.09  % Solved by: fo/fo7.sh
% 15.91/16.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.91/16.09  % done 7489 iterations in 15.647s
% 15.91/16.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.91/16.09  % SZS output start Refutation
% 15.91/16.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.91/16.09  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 15.91/16.09  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 15.91/16.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.91/16.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.91/16.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.91/16.09  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 15.91/16.09  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 15.91/16.09  thf(sk_B_type, type, sk_B: $i > $i).
% 15.91/16.09  thf(sk_A_type, type, sk_A: $i).
% 15.91/16.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 15.91/16.09  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 15.91/16.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 15.91/16.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 15.91/16.09  thf(t113_zfmisc_1, conjecture,
% 15.91/16.09    (![A:$i,B:$i]:
% 15.91/16.09     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.91/16.09       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 15.91/16.09  thf(zf_stmt_0, negated_conjecture,
% 15.91/16.09    (~( ![A:$i,B:$i]:
% 15.91/16.09        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.91/16.09          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 15.91/16.09    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 15.91/16.09  thf('0', plain,
% 15.91/16.09      ((((sk_B_1) != (k1_xboole_0))
% 15.91/16.09        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.91/16.09  thf('1', plain,
% 15.91/16.09      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 15.91/16.09       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('split', [status(esa)], ['0'])).
% 15.91/16.09  thf(d2_zfmisc_1, axiom,
% 15.91/16.09    (![A:$i,B:$i,C:$i]:
% 15.91/16.09     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 15.91/16.09       ( ![D:$i]:
% 15.91/16.09         ( ( r2_hidden @ D @ C ) <=>
% 15.91/16.09           ( ?[E:$i,F:$i]:
% 15.91/16.09             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 15.91/16.09               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 15.91/16.09  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 15.91/16.09  thf(zf_stmt_2, axiom,
% 15.91/16.09    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 15.91/16.09     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 15.91/16.09       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 15.91/16.09         ( r2_hidden @ E @ A ) ) ))).
% 15.91/16.09  thf(zf_stmt_3, axiom,
% 15.91/16.09    (![A:$i,B:$i,C:$i]:
% 15.91/16.09     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 15.91/16.09       ( ![D:$i]:
% 15.91/16.09         ( ( r2_hidden @ D @ C ) <=>
% 15.91/16.09           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 15.91/16.09  thf('2', plain,
% 15.91/16.09      (![X15 : $i, X16 : $i, X19 : $i]:
% 15.91/16.09         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 15.91/16.09          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 15.91/16.09             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 15.91/16.09          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.91/16.09  thf('3', plain,
% 15.91/16.09      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 15.91/16.09         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 15.91/16.09  thf('4', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.09         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 15.91/16.09          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 15.91/16.09          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 15.91/16.09      inference('sup-', [status(thm)], ['2', '3'])).
% 15.91/16.09  thf(t5_boole, axiom,
% 15.91/16.09    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 15.91/16.09  thf('5', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 15.91/16.09      inference('cnf', [status(esa)], [t5_boole])).
% 15.91/16.09  thf(t1_xboole_0, axiom,
% 15.91/16.09    (![A:$i,B:$i,C:$i]:
% 15.91/16.09     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 15.91/16.09       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 15.91/16.09  thf('6', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.09         (~ (r2_hidden @ X0 @ X1)
% 15.91/16.09          | ~ (r2_hidden @ X0 @ X2)
% 15.91/16.09          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 15.91/16.09      inference('cnf', [status(esa)], [t1_xboole_0])).
% 15.91/16.09  thf('7', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (~ (r2_hidden @ X1 @ X0)
% 15.91/16.09          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 15.91/16.09          | ~ (r2_hidden @ X1 @ X0))),
% 15.91/16.09      inference('sup-', [status(thm)], ['5', '6'])).
% 15.91/16.09  thf('8', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 15.91/16.09      inference('simplify', [status(thm)], ['7'])).
% 15.91/16.09  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 15.91/16.09      inference('condensation', [status(thm)], ['8'])).
% 15.91/16.09  thf('10', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 15.91/16.09          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 15.91/16.09      inference('sup-', [status(thm)], ['4', '9'])).
% 15.91/16.09  thf('11', plain,
% 15.91/16.09      ((((sk_B_1) = (k1_xboole_0))
% 15.91/16.09        | ((sk_A) = (k1_xboole_0))
% 15.91/16.09        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.91/16.09  thf('12', plain,
% 15.91/16.09      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 15.91/16.09      inference('condensation', [status(thm)], ['8'])).
% 15.91/16.09  thf('14', plain,
% 15.91/16.09      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 15.91/16.09         <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['12', '13'])).
% 15.91/16.09  thf('15', plain,
% 15.91/16.09      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 15.91/16.09         <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['10', '14'])).
% 15.91/16.09  thf('16', plain,
% 15.91/16.09      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('17', plain,
% 15.91/16.09      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 15.91/16.09         <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('demod', [status(thm)], ['15', '16'])).
% 15.91/16.09  thf('18', plain,
% 15.91/16.09      ((((sk_A) != (k1_xboole_0))
% 15.91/16.09        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.91/16.09  thf('19', plain,
% 15.91/16.09      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['18'])).
% 15.91/16.09  thf('20', plain,
% 15.91/16.09      ((((sk_B_1) != (k1_xboole_0)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 15.91/16.09             (((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['17', '19'])).
% 15.91/16.09  thf('21', plain,
% 15.91/16.09      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('22', plain,
% 15.91/16.09      ((((sk_B_1) != (sk_B_1)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 15.91/16.09             (((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('demod', [status(thm)], ['20', '21'])).
% 15.91/16.09  thf('23', plain,
% 15.91/16.09      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 15.91/16.09       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('simplify', [status(thm)], ['22'])).
% 15.91/16.09  thf('24', plain,
% 15.91/16.09      (~ (((sk_A) = (k1_xboole_0))) | 
% 15.91/16.09       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('split', [status(esa)], ['18'])).
% 15.91/16.09  thf('25', plain,
% 15.91/16.09      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 15.91/16.09         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf(t7_xboole_0, axiom,
% 15.91/16.09    (![A:$i]:
% 15.91/16.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 15.91/16.09          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 15.91/16.09  thf('26', plain,
% 15.91/16.09      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 15.91/16.09      inference('cnf', [status(esa)], [t7_xboole_0])).
% 15.91/16.09  thf('27', plain,
% 15.91/16.09      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 15.91/16.09      inference('cnf', [status(esa)], [t7_xboole_0])).
% 15.91/16.09  thf('28', plain,
% 15.91/16.09      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 15.91/16.09         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 15.91/16.09          | ~ (r2_hidden @ X6 @ X11)
% 15.91/16.09          | ~ (r2_hidden @ X7 @ X9)
% 15.91/16.09          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 15.91/16.09  thf('29', plain,
% 15.91/16.09      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 15.91/16.09         (~ (r2_hidden @ X7 @ X9)
% 15.91/16.09          | ~ (r2_hidden @ X6 @ X11)
% 15.91/16.09          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 15.91/16.09      inference('simplify', [status(thm)], ['28'])).
% 15.91/16.09  thf('30', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.09         (((X0) = (k1_xboole_0))
% 15.91/16.09          | (zip_tseitin_0 @ (sk_B @ X0) @ X2 @ 
% 15.91/16.09             (k4_tarski @ X2 @ (sk_B @ X0)) @ X0 @ X1)
% 15.91/16.09          | ~ (r2_hidden @ X2 @ X1))),
% 15.91/16.09      inference('sup-', [status(thm)], ['27', '29'])).
% 15.91/16.09  thf('31', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (((X0) = (k1_xboole_0))
% 15.91/16.09          | (zip_tseitin_0 @ (sk_B @ X1) @ (sk_B @ X0) @ 
% 15.91/16.09             (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ X1 @ X0)
% 15.91/16.09          | ((X1) = (k1_xboole_0)))),
% 15.91/16.09      inference('sup-', [status(thm)], ['26', '30'])).
% 15.91/16.09  thf('32', plain,
% 15.91/16.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 15.91/16.09         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 15.91/16.09          | (r2_hidden @ X14 @ X17)
% 15.91/16.09          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.91/16.09  thf('33', plain,
% 15.91/16.09      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 15.91/16.09         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 15.91/16.09          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 15.91/16.09      inference('simplify', [status(thm)], ['32'])).
% 15.91/16.09  thf('34', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (((X1) = (k1_xboole_0))
% 15.91/16.09          | ((X0) = (k1_xboole_0))
% 15.91/16.09          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 15.91/16.09             (k2_zfmisc_1 @ X0 @ X1)))),
% 15.91/16.09      inference('sup-', [status(thm)], ['31', '33'])).
% 15.91/16.09  thf('35', plain,
% 15.91/16.09      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 15.91/16.09          k1_xboole_0)
% 15.91/16.09         | ((sk_A) = (k1_xboole_0))
% 15.91/16.09         | ((sk_B_1) = (k1_xboole_0))))
% 15.91/16.09         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup+', [status(thm)], ['25', '34'])).
% 15.91/16.09  thf('36', plain,
% 15.91/16.09      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['0'])).
% 15.91/16.09  thf('37', plain,
% 15.91/16.09      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 15.91/16.09       ~ (((sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('simplify', [status(thm)], ['22'])).
% 15.91/16.09  thf('38', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('sat_resolution*', [status(thm)], ['1', '37'])).
% 15.91/16.09  thf('39', plain, (((sk_B_1) != (k1_xboole_0))),
% 15.91/16.09      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 15.91/16.09  thf('40', plain,
% 15.91/16.09      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 15.91/16.09          k1_xboole_0)
% 15.91/16.09         | ((sk_A) = (k1_xboole_0))))
% 15.91/16.09         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('simplify_reflect-', [status(thm)], ['35', '39'])).
% 15.91/16.09  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 15.91/16.09      inference('condensation', [status(thm)], ['8'])).
% 15.91/16.09  thf('42', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0)))
% 15.91/16.09         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('clc', [status(thm)], ['40', '41'])).
% 15.91/16.09  thf('43', plain,
% 15.91/16.09      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['18'])).
% 15.91/16.09  thf('44', plain,
% 15.91/16.09      ((((sk_A) != (sk_A)))
% 15.91/16.09         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 15.91/16.09             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['42', '43'])).
% 15.91/16.09  thf('45', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0))) | 
% 15.91/16.09       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('simplify', [status(thm)], ['44'])).
% 15.91/16.09  thf('46', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0))) | 
% 15.91/16.09       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 15.91/16.09       (((sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('47', plain,
% 15.91/16.09      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 15.91/16.09      inference('cnf', [status(esa)], [t7_xboole_0])).
% 15.91/16.09  thf('48', plain,
% 15.91/16.09      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 15.91/16.09         (~ (r2_hidden @ X18 @ X17)
% 15.91/16.09          | (zip_tseitin_0 @ (sk_F_1 @ X18 @ X15 @ X16) @ 
% 15.91/16.09             (sk_E_1 @ X18 @ X15 @ X16) @ X18 @ X15 @ X16)
% 15.91/16.09          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.91/16.09  thf('49', plain,
% 15.91/16.09      (![X15 : $i, X16 : $i, X18 : $i]:
% 15.91/16.09         ((zip_tseitin_0 @ (sk_F_1 @ X18 @ X15 @ X16) @ 
% 15.91/16.09           (sk_E_1 @ X18 @ X15 @ X16) @ X18 @ X15 @ X16)
% 15.91/16.09          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X16 @ X15)))),
% 15.91/16.09      inference('simplify', [status(thm)], ['48'])).
% 15.91/16.09  thf('50', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 15.91/16.09          | (zip_tseitin_0 @ 
% 15.91/16.09             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 15.91/16.09             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 15.91/16.09             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 15.91/16.09      inference('sup-', [status(thm)], ['47', '49'])).
% 15.91/16.09  thf('51', plain,
% 15.91/16.09      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 15.91/16.09         ((r2_hidden @ X6 @ X10) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 15.91/16.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 15.91/16.09  thf('52', plain,
% 15.91/16.09      (![X0 : $i, X1 : $i]:
% 15.91/16.09         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 15.91/16.09          | (r2_hidden @ 
% 15.91/16.09             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 15.91/16.09      inference('sup-', [status(thm)], ['50', '51'])).
% 15.91/16.09  thf('53', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 15.91/16.09      inference('condensation', [status(thm)], ['8'])).
% 15.91/16.09  thf('55', plain,
% 15.91/16.09      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['53', '54'])).
% 15.91/16.09  thf('56', plain,
% 15.91/16.09      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 15.91/16.09         <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['52', '55'])).
% 15.91/16.09  thf('57', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('58', plain,
% 15.91/16.09      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 15.91/16.09         <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('demod', [status(thm)], ['56', '57'])).
% 15.91/16.09  thf('59', plain,
% 15.91/16.09      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['18'])).
% 15.91/16.09  thf('60', plain,
% 15.91/16.09      ((((sk_A) != (k1_xboole_0)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 15.91/16.09             (((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('sup-', [status(thm)], ['58', '59'])).
% 15.91/16.09  thf('61', plain,
% 15.91/16.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('split', [status(esa)], ['11'])).
% 15.91/16.09  thf('62', plain,
% 15.91/16.09      ((((sk_A) != (sk_A)))
% 15.91/16.09         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 15.91/16.09             (((sk_A) = (k1_xboole_0))))),
% 15.91/16.09      inference('demod', [status(thm)], ['60', '61'])).
% 15.91/16.09  thf('63', plain,
% 15.91/16.09      (~ (((sk_A) = (k1_xboole_0))) | 
% 15.91/16.09       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 15.91/16.09      inference('simplify', [status(thm)], ['62'])).
% 15.91/16.09  thf('64', plain, ($false),
% 15.91/16.09      inference('sat_resolution*', [status(thm)],
% 15.91/16.09                ['1', '23', '24', '45', '46', '63'])).
% 15.91/16.09  
% 15.91/16.09  % SZS output end Refutation
% 15.91/16.09  
% 15.91/16.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
