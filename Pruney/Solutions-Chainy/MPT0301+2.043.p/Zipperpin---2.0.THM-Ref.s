%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5z2hmsiGQZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 264 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  868 (2508 expanded)
%              Number of equality atoms :  129 ( 402 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
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
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( X14
        = ( k2_zfmisc_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X14 @ X10 @ X11 ) @ ( sk_E @ X14 @ X10 @ X11 ) @ ( sk_D @ X14 @ X10 @ X11 ) @ X10 @ X11 )
      | ( r2_hidden @ ( sk_D @ X14 @ X10 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ X4 )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X19 )
      | ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('17',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( X14
        = ( k2_zfmisc_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X14 @ X10 @ X11 ) @ ( sk_E @ X14 @ X10 @ X11 ) @ ( sk_D @ X14 @ X10 @ X11 ) @ X10 @ X11 )
      | ( r2_hidden @ ( sk_D @ X14 @ X10 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X1 @ X5 )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X6 )
      | ~ ( r2_hidden @ X1 @ X6 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( X3
       != ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X1 @ X6 )
      | ( zip_tseitin_0 @ X2 @ X1 @ ( k4_tarski @ X1 @ X2 ) @ X4 @ X6 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X11 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X3 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','53'])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','56'])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('73',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('78',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('80',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','64','65','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5z2hmsiGQZ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 191 iterations in 0.143s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.60  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(t113_zfmisc_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.60          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((((sk_B) != (k1_xboole_0))
% 0.40/0.60        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.40/0.60       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf(d2_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.40/0.60       ( ![D:$i]:
% 0.40/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.60           ( ?[E:$i,F:$i]:
% 0.40/0.60             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.40/0.60               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.40/0.60  thf(zf_stmt_2, axiom,
% 0.40/0.60    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.40/0.60     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.40/0.60       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.40/0.60         ( r2_hidden @ E @ A ) ) ))).
% 0.40/0.60  thf(zf_stmt_3, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.40/0.60       ( ![D:$i]:
% 0.40/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.60           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.40/0.60         (((X14) = (k2_zfmisc_1 @ X11 @ X10))
% 0.40/0.60          | (zip_tseitin_0 @ (sk_F @ X14 @ X10 @ X11) @ 
% 0.40/0.60             (sk_E @ X14 @ X10 @ X11) @ (sk_D @ X14 @ X10 @ X11) @ X10 @ X11)
% 0.40/0.60          | (r2_hidden @ (sk_D @ X14 @ X10 @ X11) @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.60         ((r2_hidden @ X2 @ X4) | ~ (zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X5))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.40/0.60          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.40/0.60          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf(t4_boole, axiom,
% 0.40/0.60    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.60  thf(t64_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.40/0.60       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.60         (((X17) != (X19))
% 0.40/0.60          | ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19))))),
% 0.40/0.60      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.60  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.40/0.60          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))
% 0.40/0.60        | ((sk_A) = (k1_xboole_0))
% 0.40/0.60        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))
% 0.40/0.60         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.40/0.60         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.60         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['9', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.60         <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      ((((sk_A) != (k1_xboole_0))
% 0.40/0.60        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      ((((sk_B) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.40/0.60             (((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['20', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      ((((sk_B) != (sk_B)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.40/0.60             (((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.40/0.60       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.40/0.60       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('split', [status(esa)], ['21'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.40/0.60         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.40/0.60         (((X14) = (k2_zfmisc_1 @ X11 @ X10))
% 0.40/0.60          | (zip_tseitin_0 @ (sk_F @ X14 @ X10 @ X11) @ 
% 0.40/0.60             (sk_E @ X14 @ X10 @ X11) @ (sk_D @ X14 @ X10 @ X11) @ X10 @ X11)
% 0.40/0.60          | (r2_hidden @ (sk_D @ X14 @ X10 @ X11) @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.60         ((r2_hidden @ X1 @ X5) | ~ (zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X5))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.40/0.60          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.40/0.60          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.40/0.60          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.40/0.60          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.60  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X1) = (k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.40/0.60      inference('demod', [status(thm)], ['33', '38'])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.40/0.60          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.40/0.60          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.40/0.60          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '8'])).
% 0.40/0.60  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X1) = (k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.40/0.60      inference('demod', [status(thm)], ['42', '45'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X6 : $i]:
% 0.40/0.60         ((zip_tseitin_0 @ X2 @ X1 @ X3 @ X4 @ X6)
% 0.40/0.60          | ~ (r2_hidden @ X1 @ X6)
% 0.40/0.60          | ~ (r2_hidden @ X2 @ X4)
% 0.40/0.60          | ((X3) != (k4_tarski @ X1 @ X2)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X4 : $i, X6 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X2 @ X4)
% 0.40/0.60          | ~ (r2_hidden @ X1 @ X6)
% 0.40/0.60          | (zip_tseitin_0 @ X2 @ X1 @ (k4_tarski @ X1 @ X2) @ X4 @ X6))),
% 0.40/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | (zip_tseitin_0 @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X3 @ 
% 0.40/0.60             (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ X0 @ X2)
% 0.40/0.60          | ~ (r2_hidden @ X3 @ X2))),
% 0.40/0.60      inference('sup-', [status(thm)], ['46', '48'])).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | (zip_tseitin_0 @ (sk_D @ X2 @ k1_xboole_0 @ X3) @ 
% 0.40/0.60             (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 0.40/0.60             (k4_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 0.40/0.60              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.40/0.60             X2 @ X0)
% 0.40/0.60          | ((X2) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['39', '49'])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.40/0.60          | (r2_hidden @ X9 @ X12)
% 0.40/0.60          | ((X12) != (k2_zfmisc_1 @ X11 @ X10)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.60         ((r2_hidden @ X9 @ (k2_zfmisc_1 @ X11 @ X10))
% 0.40/0.60          | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X11))),
% 0.40/0.60      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (((X1) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ 
% 0.40/0.60             (k4_tarski @ (sk_D @ X0 @ X3 @ k1_xboole_0) @ 
% 0.40/0.60              (sk_D @ X1 @ k1_xboole_0 @ X2)) @ 
% 0.40/0.60             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['50', '52'])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      ((![X0 : $i, X1 : $i]:
% 0.40/0.60          ((r2_hidden @ 
% 0.40/0.60            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.40/0.60             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.40/0.60            k1_xboole_0)
% 0.40/0.60           | ((sk_A) = (k1_xboole_0))
% 0.40/0.60           | ((sk_B) = (k1_xboole_0))))
% 0.40/0.60         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['28', '53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.40/0.60       ~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.60  thf('57', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['1', '56'])).
% 0.40/0.60  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((![X0 : $i, X1 : $i]:
% 0.40/0.60          ((r2_hidden @ 
% 0.40/0.60            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.40/0.60             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.40/0.60            k1_xboole_0)
% 0.40/0.60           | ((sk_A) = (k1_xboole_0))))
% 0.40/0.60         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['54', '58'])).
% 0.40/0.60  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0)))
% 0.40/0.60         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('clc', [status(thm)], ['59', '60'])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['21'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      ((((sk_A) != (sk_A)))
% 0.40/0.60         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.40/0.60             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) | 
% 0.40/0.60       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) | 
% 0.40/0.60       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.40/0.60       (((sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.40/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['67', '68'])).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.40/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['66', '73'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('76', plain,
% 0.40/0.60      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.60  thf('77', plain,
% 0.40/0.60      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['21'])).
% 0.40/0.60  thf('78', plain,
% 0.40/0.60      ((((sk_A) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.40/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['76', '77'])).
% 0.40/0.60  thf('79', plain,
% 0.40/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      ((((sk_A) != (sk_A)))
% 0.40/0.60         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.40/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['78', '79'])).
% 0.40/0.60  thf('81', plain,
% 0.40/0.60      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.40/0.60       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['80'])).
% 0.40/0.60  thf('82', plain, ($false),
% 0.40/0.60      inference('sat_resolution*', [status(thm)],
% 0.40/0.60                ['1', '26', '27', '64', '65', '81'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
