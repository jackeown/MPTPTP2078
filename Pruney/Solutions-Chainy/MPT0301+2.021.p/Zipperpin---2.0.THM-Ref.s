%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MAGBr9xuVI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:02 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 156 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  719 (1367 expanded)
%              Number of equality atoms :  117 ( 240 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X26: $i,X27: $i,X30: $i] :
      ( ( X30
        = ( k2_zfmisc_1 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X30 @ X26 @ X27 ) @ ( sk_E @ X30 @ X26 @ X27 ) @ ( sk_D_1 @ X30 @ X26 @ X27 ) @ X26 @ X27 )
      | ( r2_hidden @ ( sk_D_1 @ X30 @ X26 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X20 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
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

thf('11',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
       != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('26',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X37 ) )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('37',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('42',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X26: $i,X27: $i,X30: $i] :
      ( ( X30
        = ( k2_zfmisc_1 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X30 @ X26 @ X27 ) @ ( sk_E @ X30 @ X26 @ X27 ) @ ( sk_D_1 @ X30 @ X26 @ X27 ) @ X26 @ X27 )
      | ( r2_hidden @ ( sk_D_1 @ X30 @ X26 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X17 @ X21 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B_1 )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B_1 )
       != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0 != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('60',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','43','61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MAGBr9xuVI
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.31/2.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.31/2.55  % Solved by: fo/fo7.sh
% 2.31/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.55  % done 2565 iterations in 2.050s
% 2.31/2.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.31/2.55  % SZS output start Refutation
% 2.31/2.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.31/2.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.31/2.55  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 2.31/2.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.31/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.31/2.55  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.31/2.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.31/2.55  thf(sk_B_type, type, sk_B: $i > $i).
% 2.31/2.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.31/2.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.31/2.55  thf(t113_zfmisc_1, conjecture,
% 2.31/2.55    (![A:$i,B:$i]:
% 2.31/2.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.31/2.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.31/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.55    (~( ![A:$i,B:$i]:
% 2.31/2.55        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.31/2.55          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 2.31/2.55    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 2.31/2.55  thf('0', plain,
% 2.31/2.55      ((((sk_B_1) != (k1_xboole_0))
% 2.31/2.55        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('1', plain,
% 2.31/2.55      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 2.31/2.55       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 2.31/2.55      inference('split', [status(esa)], ['0'])).
% 2.31/2.55  thf(d2_zfmisc_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.31/2.55       ( ![D:$i]:
% 2.31/2.55         ( ( r2_hidden @ D @ C ) <=>
% 2.31/2.55           ( ?[E:$i,F:$i]:
% 2.31/2.55             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.31/2.55               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.31/2.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.31/2.55  thf(zf_stmt_2, axiom,
% 2.31/2.55    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.31/2.55     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.31/2.55       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.31/2.55         ( r2_hidden @ E @ A ) ) ))).
% 2.31/2.55  thf(zf_stmt_3, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.31/2.55       ( ![D:$i]:
% 2.31/2.55         ( ( r2_hidden @ D @ C ) <=>
% 2.31/2.55           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.31/2.55  thf('2', plain,
% 2.31/2.55      (![X26 : $i, X27 : $i, X30 : $i]:
% 2.31/2.55         (((X30) = (k2_zfmisc_1 @ X27 @ X26))
% 2.31/2.55          | (zip_tseitin_0 @ (sk_F @ X30 @ X26 @ X27) @ 
% 2.31/2.55             (sk_E @ X30 @ X26 @ X27) @ (sk_D_1 @ X30 @ X26 @ X27) @ X26 @ X27)
% 2.31/2.55          | (r2_hidden @ (sk_D_1 @ X30 @ X26 @ X27) @ X30))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.31/2.55  thf('3', plain,
% 2.31/2.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.31/2.55         ((r2_hidden @ X18 @ X20)
% 2.31/2.55          | ~ (zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.31/2.55  thf('4', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 2.31/2.55          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 2.31/2.55          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 2.31/2.55      inference('sup-', [status(thm)], ['2', '3'])).
% 2.31/2.55  thf(t92_xboole_1, axiom,
% 2.31/2.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.31/2.55  thf('5', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 2.31/2.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.31/2.55  thf(t1_xboole_0, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 2.31/2.55       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 2.31/2.55  thf('6', plain,
% 2.31/2.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.31/2.55         (~ (r2_hidden @ X6 @ X7)
% 2.31/2.55          | ~ (r2_hidden @ X6 @ X8)
% 2.31/2.55          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 2.31/2.55      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.31/2.55  thf('7', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 2.31/2.55          | ~ (r2_hidden @ X1 @ X0)
% 2.31/2.55          | ~ (r2_hidden @ X1 @ X0))),
% 2.31/2.55      inference('sup-', [status(thm)], ['5', '6'])).
% 2.31/2.55  thf('8', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.31/2.55      inference('simplify', [status(thm)], ['7'])).
% 2.31/2.55  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.31/2.55      inference('condensation', [status(thm)], ['8'])).
% 2.31/2.55  thf('10', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.55          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['4', '9'])).
% 2.31/2.55  thf('11', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 2.31/2.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.31/2.55  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.31/2.55      inference('condensation', [status(thm)], ['8'])).
% 2.31/2.55  thf('13', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.55      inference('sup-', [status(thm)], ['11', '12'])).
% 2.31/2.55  thf('14', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['10', '13'])).
% 2.31/2.55  thf('15', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 2.31/2.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.31/2.55  thf('16', plain,
% 2.31/2.55      ((((sk_B_1) = (k1_xboole_0))
% 2.31/2.55        | ((sk_A) = (k1_xboole_0))
% 2.31/2.55        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('17', plain,
% 2.31/2.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['16'])).
% 2.31/2.55  thf('18', plain,
% 2.31/2.55      ((![X0 : $i]: ((sk_B_1) = (k5_xboole_0 @ X0 @ X0)))
% 2.31/2.55         <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup+', [status(thm)], ['15', '17'])).
% 2.31/2.55  thf('19', plain,
% 2.31/2.55      ((((sk_A) != (k1_xboole_0))
% 2.31/2.55        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('20', plain,
% 2.31/2.55      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['19'])).
% 2.31/2.55  thf('21', plain,
% 2.31/2.55      ((![X0 : $i]:
% 2.31/2.55          ((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['18', '20'])).
% 2.31/2.55  thf('22', plain,
% 2.31/2.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['16'])).
% 2.31/2.55  thf('23', plain,
% 2.31/2.55      ((![X0 : $i]:
% 2.31/2.55          ((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (sk_B_1)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('demod', [status(thm)], ['21', '22'])).
% 2.31/2.55  thf('24', plain,
% 2.31/2.55      ((((k1_xboole_0) != (sk_B_1)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['14', '23'])).
% 2.31/2.55  thf('25', plain,
% 2.31/2.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['16'])).
% 2.31/2.55  thf('26', plain,
% 2.31/2.55      ((((sk_B_1) != (sk_B_1)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('demod', [status(thm)], ['24', '25'])).
% 2.31/2.55  thf('27', plain,
% 2.31/2.55      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 2.31/2.55       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 2.31/2.55      inference('simplify', [status(thm)], ['26'])).
% 2.31/2.55  thf('28', plain,
% 2.31/2.55      (~ (((sk_A) = (k1_xboole_0))) | 
% 2.31/2.55       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 2.31/2.55      inference('split', [status(esa)], ['19'])).
% 2.31/2.55  thf('29', plain,
% 2.31/2.55      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 2.31/2.55         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['16'])).
% 2.31/2.55  thf(t7_xboole_0, axiom,
% 2.31/2.55    (![A:$i]:
% 2.31/2.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.31/2.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.31/2.55  thf('30', plain,
% 2.31/2.55      (![X10 : $i]:
% 2.31/2.55         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 2.31/2.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.31/2.55  thf('31', plain,
% 2.31/2.55      (![X10 : $i]:
% 2.31/2.55         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 2.31/2.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.31/2.55  thf(t106_zfmisc_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.55     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.31/2.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.31/2.55  thf('32', plain,
% 2.31/2.55      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 2.31/2.55         ((r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X37))
% 2.31/2.55          | ~ (r2_hidden @ X35 @ X37)
% 2.31/2.55          | ~ (r2_hidden @ X33 @ X34))),
% 2.31/2.55      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 2.31/2.55  thf('33', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         (((X0) = (k1_xboole_0))
% 2.31/2.55          | ~ (r2_hidden @ X2 @ X1)
% 2.31/2.55          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 2.31/2.55             (k2_zfmisc_1 @ X1 @ X0)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['31', '32'])).
% 2.31/2.55  thf('34', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         (((X0) = (k1_xboole_0))
% 2.31/2.55          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 2.31/2.55             (k2_zfmisc_1 @ X0 @ X1))
% 2.31/2.55          | ((X1) = (k1_xboole_0)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['30', '33'])).
% 2.31/2.55  thf('35', plain,
% 2.31/2.55      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.31/2.55          k1_xboole_0)
% 2.31/2.55         | ((sk_B_1) = (k1_xboole_0))
% 2.31/2.55         | ((sk_A) = (k1_xboole_0))))
% 2.31/2.55         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup+', [status(thm)], ['29', '34'])).
% 2.31/2.55  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.31/2.55      inference('condensation', [status(thm)], ['8'])).
% 2.31/2.55  thf('37', plain,
% 2.31/2.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 2.31/2.55         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('clc', [status(thm)], ['35', '36'])).
% 2.31/2.55  thf('38', plain,
% 2.31/2.55      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['0'])).
% 2.31/2.55  thf('39', plain,
% 2.31/2.55      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 2.31/2.55         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['37', '38'])).
% 2.31/2.55  thf('40', plain,
% 2.31/2.55      ((((sk_A) = (k1_xboole_0)))
% 2.31/2.55         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('simplify', [status(thm)], ['39'])).
% 2.31/2.55  thf('41', plain,
% 2.31/2.55      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['19'])).
% 2.31/2.55  thf('42', plain,
% 2.31/2.55      ((((sk_A) != (sk_A)))
% 2.31/2.55         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             ~ (((sk_A) = (k1_xboole_0))) & 
% 2.31/2.55             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['40', '41'])).
% 2.31/2.55  thf('43', plain,
% 2.31/2.55      ((((sk_A) = (k1_xboole_0))) | 
% 2.31/2.55       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 2.31/2.55       (((sk_B_1) = (k1_xboole_0)))),
% 2.31/2.55      inference('simplify', [status(thm)], ['42'])).
% 2.31/2.55  thf('44', plain,
% 2.31/2.55      (![X26 : $i, X27 : $i, X30 : $i]:
% 2.31/2.55         (((X30) = (k2_zfmisc_1 @ X27 @ X26))
% 2.31/2.55          | (zip_tseitin_0 @ (sk_F @ X30 @ X26 @ X27) @ 
% 2.31/2.55             (sk_E @ X30 @ X26 @ X27) @ (sk_D_1 @ X30 @ X26 @ X27) @ X26 @ X27)
% 2.31/2.55          | (r2_hidden @ (sk_D_1 @ X30 @ X26 @ X27) @ X30))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.31/2.55  thf('45', plain,
% 2.31/2.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.31/2.55         ((r2_hidden @ X17 @ X21)
% 2.31/2.55          | ~ (zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.31/2.55  thf('46', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 2.31/2.55          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 2.31/2.55          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 2.31/2.55      inference('sup-', [status(thm)], ['44', '45'])).
% 2.31/2.55  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.31/2.55      inference('condensation', [status(thm)], ['8'])).
% 2.31/2.55  thf('48', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 2.31/2.55          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['46', '47'])).
% 2.31/2.55  thf('49', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.55      inference('sup-', [status(thm)], ['11', '12'])).
% 2.31/2.55  thf('50', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         ((k1_xboole_0) = (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 2.31/2.55      inference('sup-', [status(thm)], ['48', '49'])).
% 2.31/2.55  thf('51', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 2.31/2.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.31/2.55  thf('52', plain,
% 2.31/2.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['16'])).
% 2.31/2.55  thf('53', plain,
% 2.31/2.55      ((![X0 : $i]: ((sk_A) = (k5_xboole_0 @ X0 @ X0)))
% 2.31/2.55         <= ((((sk_A) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup+', [status(thm)], ['51', '52'])).
% 2.31/2.55  thf('54', plain,
% 2.31/2.55      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 2.31/2.55      inference('split', [status(esa)], ['19'])).
% 2.31/2.55  thf('55', plain,
% 2.31/2.55      ((![X0 : $i]:
% 2.31/2.55          ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ sk_B_1) != (k1_xboole_0)))
% 2.31/2.55         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.55             (((sk_A) = (k1_xboole_0))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('56', plain,
% 2.31/2.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.31/2.56      inference('split', [status(esa)], ['16'])).
% 2.31/2.56  thf('57', plain,
% 2.31/2.56      ((![X0 : $i]:
% 2.31/2.56          ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ sk_B_1) != (sk_A)))
% 2.31/2.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.56             (((sk_A) = (k1_xboole_0))))),
% 2.31/2.56      inference('demod', [status(thm)], ['55', '56'])).
% 2.31/2.56  thf('58', plain,
% 2.31/2.56      ((((k1_xboole_0) != (sk_A)))
% 2.31/2.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.56             (((sk_A) = (k1_xboole_0))))),
% 2.31/2.56      inference('sup-', [status(thm)], ['50', '57'])).
% 2.31/2.56  thf('59', plain,
% 2.31/2.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.31/2.56      inference('split', [status(esa)], ['16'])).
% 2.31/2.56  thf('60', plain,
% 2.31/2.56      ((((sk_A) != (sk_A)))
% 2.31/2.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 2.31/2.56             (((sk_A) = (k1_xboole_0))))),
% 2.31/2.56      inference('demod', [status(thm)], ['58', '59'])).
% 2.31/2.56  thf('61', plain,
% 2.31/2.56      (~ (((sk_A) = (k1_xboole_0))) | 
% 2.31/2.56       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 2.31/2.56      inference('simplify', [status(thm)], ['60'])).
% 2.31/2.56  thf('62', plain,
% 2.31/2.56      ((((sk_A) = (k1_xboole_0))) | 
% 2.31/2.56       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 2.31/2.56       (((sk_B_1) = (k1_xboole_0)))),
% 2.31/2.56      inference('split', [status(esa)], ['16'])).
% 2.31/2.56  thf('63', plain, ($false),
% 2.31/2.56      inference('sat_resolution*', [status(thm)],
% 2.31/2.56                ['1', '27', '28', '43', '61', '62'])).
% 2.31/2.56  
% 2.31/2.56  % SZS output end Refutation
% 2.31/2.56  
% 2.31/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
