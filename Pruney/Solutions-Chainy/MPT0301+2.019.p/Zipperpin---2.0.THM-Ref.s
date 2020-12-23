%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZkDONp5OQ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 5.04s
% Output     : Refutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 285 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  785 (2321 expanded)
%              Number of equality atoms :  114 ( 356 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('18',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X30: $i] :
      ( ( X30
        = ( k3_tarski @ X26 ) )
      | ( r2_hidden @ ( sk_D_1 @ X30 @ X26 ) @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X26 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('31',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('33',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X14 )
      | ~ ( r2_hidden @ X9 @ X14 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ( X11
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X9 @ X14 )
      | ( zip_tseitin_0 @ X10 @ X9 @ ( k4_tarski @ X9 @ X10 ) @ X12 @ X14 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X17 @ X20 )
      | ( X20
       != ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','45'])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('52',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X9 @ X13 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('61',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('62',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('67',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('69',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','53','54','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZkDONp5OQ
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:37:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 5.04/5.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.04/5.26  % Solved by: fo/fo7.sh
% 5.04/5.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.04/5.26  % done 2451 iterations in 4.787s
% 5.04/5.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.04/5.26  % SZS output start Refutation
% 5.04/5.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.04/5.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.04/5.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.04/5.26  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 5.04/5.26  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 5.04/5.26  thf(sk_A_type, type, sk_A: $i).
% 5.04/5.26  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.04/5.26  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.04/5.26  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.04/5.26  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.04/5.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.04/5.26  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 5.04/5.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.04/5.26  thf(sk_B_type, type, sk_B: $i).
% 5.04/5.26  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.04/5.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.04/5.26  thf(t113_zfmisc_1, conjecture,
% 5.04/5.26    (![A:$i,B:$i]:
% 5.04/5.26     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.04/5.26       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.04/5.26  thf(zf_stmt_0, negated_conjecture,
% 5.04/5.26    (~( ![A:$i,B:$i]:
% 5.04/5.26        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.04/5.26          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 5.04/5.26    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 5.04/5.26  thf('0', plain,
% 5.04/5.26      ((((sk_B) != (k1_xboole_0))
% 5.04/5.26        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.26  thf('1', plain,
% 5.04/5.26      (~ (((sk_B) = (k1_xboole_0))) | 
% 5.04/5.26       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('split', [status(esa)], ['0'])).
% 5.04/5.26  thf(d2_zfmisc_1, axiom,
% 5.04/5.26    (![A:$i,B:$i,C:$i]:
% 5.04/5.26     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.04/5.26       ( ![D:$i]:
% 5.04/5.26         ( ( r2_hidden @ D @ C ) <=>
% 5.04/5.26           ( ?[E:$i,F:$i]:
% 5.04/5.26             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 5.04/5.26               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 5.04/5.26  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 5.04/5.26  thf(zf_stmt_2, axiom,
% 5.04/5.26    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 5.04/5.26     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 5.04/5.26       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 5.04/5.26         ( r2_hidden @ E @ A ) ) ))).
% 5.04/5.26  thf(zf_stmt_3, axiom,
% 5.04/5.26    (![A:$i,B:$i,C:$i]:
% 5.04/5.26     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.04/5.26       ( ![D:$i]:
% 5.04/5.26         ( ( r2_hidden @ D @ C ) <=>
% 5.04/5.26           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 5.04/5.26  thf('2', plain,
% 5.04/5.26      (![X18 : $i, X19 : $i, X22 : $i]:
% 5.04/5.26         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 5.04/5.26          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 5.04/5.26             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 5.04/5.26          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.04/5.26  thf('3', plain,
% 5.04/5.26      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.04/5.26         ((r2_hidden @ X10 @ X12)
% 5.04/5.26          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.26  thf('4', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.04/5.26          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.04/5.26          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 5.04/5.26      inference('sup-', [status(thm)], ['2', '3'])).
% 5.04/5.26  thf(t48_xboole_1, axiom,
% 5.04/5.26    (![A:$i,B:$i]:
% 5.04/5.26     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.04/5.26  thf('5', plain,
% 5.04/5.26      (![X4 : $i, X5 : $i]:
% 5.04/5.26         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 5.04/5.26           = (k3_xboole_0 @ X4 @ X5))),
% 5.04/5.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.04/5.26  thf(t4_boole, axiom,
% 5.04/5.26    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 5.04/5.26  thf('6', plain,
% 5.04/5.26      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.04/5.26      inference('cnf', [status(esa)], [t4_boole])).
% 5.04/5.26  thf('7', plain,
% 5.04/5.26      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.04/5.26      inference('sup+', [status(thm)], ['5', '6'])).
% 5.04/5.26  thf(t4_xboole_0, axiom,
% 5.04/5.26    (![A:$i,B:$i]:
% 5.04/5.26     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 5.04/5.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.04/5.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.04/5.26            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 5.04/5.26  thf('8', plain,
% 5.04/5.26      (![X0 : $i, X2 : $i, X3 : $i]:
% 5.04/5.26         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 5.04/5.26          | ~ (r1_xboole_0 @ X0 @ X3))),
% 5.04/5.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 5.04/5.26  thf('9', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i]:
% 5.04/5.26         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 5.04/5.26      inference('sup-', [status(thm)], ['7', '8'])).
% 5.04/5.26  thf('10', plain,
% 5.04/5.26      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.04/5.26      inference('cnf', [status(esa)], [t4_boole])).
% 5.04/5.26  thf(t79_xboole_1, axiom,
% 5.04/5.26    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.04/5.26  thf('11', plain,
% 5.04/5.26      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 5.04/5.26      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.04/5.26  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.04/5.26      inference('sup+', [status(thm)], ['10', '11'])).
% 5.04/5.26  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('14', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 5.04/5.26          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 5.04/5.26      inference('sup-', [status(thm)], ['4', '13'])).
% 5.04/5.26  thf('15', plain,
% 5.04/5.26      ((((sk_B) = (k1_xboole_0))
% 5.04/5.26        | ((sk_A) = (k1_xboole_0))
% 5.04/5.26        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.26  thf('16', plain,
% 5.04/5.26      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('18', plain,
% 5.04/5.26      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['16', '17'])).
% 5.04/5.26  thf('19', plain,
% 5.04/5.26      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 5.04/5.26         <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['14', '18'])).
% 5.04/5.26  thf('20', plain,
% 5.04/5.26      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('21', plain,
% 5.04/5.26      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 5.04/5.26         <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('demod', [status(thm)], ['19', '20'])).
% 5.04/5.26  thf('22', plain,
% 5.04/5.26      ((((sk_A) != (k1_xboole_0))
% 5.04/5.26        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.26  thf('23', plain,
% 5.04/5.26      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['22'])).
% 5.04/5.26  thf('24', plain,
% 5.04/5.26      ((((sk_B) != (k1_xboole_0)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.04/5.26             (((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['21', '23'])).
% 5.04/5.26  thf('25', plain,
% 5.04/5.26      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('26', plain,
% 5.04/5.26      ((((sk_B) != (sk_B)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.04/5.26             (((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('demod', [status(thm)], ['24', '25'])).
% 5.04/5.26  thf('27', plain,
% 5.04/5.26      (~ (((sk_B) = (k1_xboole_0))) | 
% 5.04/5.26       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('simplify', [status(thm)], ['26'])).
% 5.04/5.26  thf('28', plain,
% 5.04/5.26      (~ (((sk_A) = (k1_xboole_0))) | 
% 5.04/5.26       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('split', [status(esa)], ['22'])).
% 5.04/5.26  thf('29', plain,
% 5.04/5.26      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 5.04/5.26         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf(d4_tarski, axiom,
% 5.04/5.26    (![A:$i,B:$i]:
% 5.04/5.26     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 5.04/5.26       ( ![C:$i]:
% 5.04/5.26         ( ( r2_hidden @ C @ B ) <=>
% 5.04/5.26           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 5.04/5.26  thf('30', plain,
% 5.04/5.26      (![X26 : $i, X30 : $i]:
% 5.04/5.26         (((X30) = (k3_tarski @ X26))
% 5.04/5.26          | (r2_hidden @ (sk_D_1 @ X30 @ X26) @ X26)
% 5.04/5.26          | (r2_hidden @ (sk_C_1 @ X30 @ X26) @ X30))),
% 5.04/5.26      inference('cnf', [status(esa)], [d4_tarski])).
% 5.04/5.26  thf('31', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('32', plain,
% 5.04/5.26      (![X0 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.04/5.26          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.04/5.26      inference('sup-', [status(thm)], ['30', '31'])).
% 5.04/5.26  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 5.04/5.26  thf('33', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 5.04/5.26      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 5.04/5.26  thf('34', plain,
% 5.04/5.26      (![X0 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.04/5.26          | ((X0) = (k1_xboole_0)))),
% 5.04/5.26      inference('demod', [status(thm)], ['32', '33'])).
% 5.04/5.26  thf('35', plain,
% 5.04/5.26      (![X0 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.04/5.26          | ((X0) = (k1_xboole_0)))),
% 5.04/5.26      inference('demod', [status(thm)], ['32', '33'])).
% 5.04/5.26  thf('36', plain,
% 5.04/5.26      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 5.04/5.26         ((zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X14)
% 5.04/5.26          | ~ (r2_hidden @ X9 @ X14)
% 5.04/5.26          | ~ (r2_hidden @ X10 @ X12)
% 5.04/5.26          | ((X11) != (k4_tarski @ X9 @ X10)))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.26  thf('37', plain,
% 5.04/5.26      (![X9 : $i, X10 : $i, X12 : $i, X14 : $i]:
% 5.04/5.26         (~ (r2_hidden @ X10 @ X12)
% 5.04/5.26          | ~ (r2_hidden @ X9 @ X14)
% 5.04/5.26          | (zip_tseitin_0 @ X10 @ X9 @ (k4_tarski @ X9 @ X10) @ X12 @ X14))),
% 5.04/5.26      inference('simplify', [status(thm)], ['36'])).
% 5.04/5.26  thf('38', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.26         (((X0) = (k1_xboole_0))
% 5.04/5.26          | (zip_tseitin_0 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X2 @ 
% 5.04/5.26             (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0 @ X1)
% 5.04/5.26          | ~ (r2_hidden @ X2 @ X1))),
% 5.04/5.26      inference('sup-', [status(thm)], ['35', '37'])).
% 5.04/5.26  thf('39', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i]:
% 5.04/5.26         (((X0) = (k1_xboole_0))
% 5.04/5.26          | (zip_tseitin_0 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 5.04/5.26             (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 5.04/5.26             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 5.04/5.26              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 5.04/5.26             X1 @ X0)
% 5.04/5.26          | ((X1) = (k1_xboole_0)))),
% 5.04/5.26      inference('sup-', [status(thm)], ['34', '38'])).
% 5.04/5.26  thf('40', plain,
% 5.04/5.26      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 5.04/5.26         (~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19)
% 5.04/5.26          | (r2_hidden @ X17 @ X20)
% 5.04/5.26          | ((X20) != (k2_zfmisc_1 @ X19 @ X18)))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.04/5.26  thf('41', plain,
% 5.04/5.26      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.04/5.26         ((r2_hidden @ X17 @ (k2_zfmisc_1 @ X19 @ X18))
% 5.04/5.26          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 5.04/5.26      inference('simplify', [status(thm)], ['40'])).
% 5.04/5.26  thf('42', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i]:
% 5.04/5.26         (((X1) = (k1_xboole_0))
% 5.04/5.26          | ((X0) = (k1_xboole_0))
% 5.04/5.26          | (r2_hidden @ 
% 5.04/5.26             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 5.04/5.26              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 5.04/5.26             (k2_zfmisc_1 @ X0 @ X1)))),
% 5.04/5.26      inference('sup-', [status(thm)], ['39', '41'])).
% 5.04/5.26  thf('43', plain,
% 5.04/5.26      ((((r2_hidden @ 
% 5.04/5.26          (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 5.04/5.26           (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 5.04/5.26          k1_xboole_0)
% 5.04/5.26         | ((sk_A) = (k1_xboole_0))
% 5.04/5.26         | ((sk_B) = (k1_xboole_0))))
% 5.04/5.26         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup+', [status(thm)], ['29', '42'])).
% 5.04/5.26  thf('44', plain,
% 5.04/5.26      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['0'])).
% 5.04/5.26  thf('45', plain,
% 5.04/5.26      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 5.04/5.26       ~ (((sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('simplify', [status(thm)], ['26'])).
% 5.04/5.26  thf('46', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('sat_resolution*', [status(thm)], ['1', '45'])).
% 5.04/5.26  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 5.04/5.26      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 5.04/5.26  thf('48', plain,
% 5.04/5.26      ((((r2_hidden @ 
% 5.04/5.26          (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 5.04/5.26           (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 5.04/5.26          k1_xboole_0)
% 5.04/5.26         | ((sk_A) = (k1_xboole_0))))
% 5.04/5.26         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('simplify_reflect-', [status(thm)], ['43', '47'])).
% 5.04/5.26  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('50', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0)))
% 5.04/5.26         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('clc', [status(thm)], ['48', '49'])).
% 5.04/5.26  thf('51', plain,
% 5.04/5.26      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['22'])).
% 5.04/5.26  thf('52', plain,
% 5.04/5.26      ((((sk_A) != (sk_A)))
% 5.04/5.26         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 5.04/5.26             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['50', '51'])).
% 5.04/5.26  thf('53', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0))) | 
% 5.04/5.26       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('simplify', [status(thm)], ['52'])).
% 5.04/5.26  thf('54', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0))) | 
% 5.04/5.26       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 5.04/5.26       (((sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('55', plain,
% 5.04/5.26      (![X18 : $i, X19 : $i, X22 : $i]:
% 5.04/5.26         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 5.04/5.26          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 5.04/5.26             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 5.04/5.26          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.04/5.26  thf('56', plain,
% 5.04/5.26      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.04/5.26         ((r2_hidden @ X9 @ X13)
% 5.04/5.26          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 5.04/5.26      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.26  thf('57', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.04/5.26          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.04/5.26          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 5.04/5.26      inference('sup-', [status(thm)], ['55', '56'])).
% 5.04/5.26  thf('58', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('59', plain,
% 5.04/5.26      (![X0 : $i, X1 : $i]:
% 5.04/5.26         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.04/5.26          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 5.04/5.26      inference('sup-', [status(thm)], ['57', '58'])).
% 5.04/5.26  thf('60', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('61', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.04/5.26      inference('demod', [status(thm)], ['9', '12'])).
% 5.04/5.26  thf('62', plain,
% 5.04/5.26      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['60', '61'])).
% 5.04/5.26  thf('63', plain,
% 5.04/5.26      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 5.04/5.26         <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['59', '62'])).
% 5.04/5.26  thf('64', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('65', plain,
% 5.04/5.26      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 5.04/5.26         <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('demod', [status(thm)], ['63', '64'])).
% 5.04/5.26  thf('66', plain,
% 5.04/5.26      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['22'])).
% 5.04/5.26  thf('67', plain,
% 5.04/5.26      ((((sk_A) != (k1_xboole_0)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.04/5.26             (((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('sup-', [status(thm)], ['65', '66'])).
% 5.04/5.26  thf('68', plain,
% 5.04/5.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('split', [status(esa)], ['15'])).
% 5.04/5.26  thf('69', plain,
% 5.04/5.26      ((((sk_A) != (sk_A)))
% 5.04/5.26         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.04/5.26             (((sk_A) = (k1_xboole_0))))),
% 5.04/5.26      inference('demod', [status(thm)], ['67', '68'])).
% 5.04/5.26  thf('70', plain,
% 5.04/5.26      (~ (((sk_A) = (k1_xboole_0))) | 
% 5.04/5.26       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.04/5.26      inference('simplify', [status(thm)], ['69'])).
% 5.04/5.26  thf('71', plain, ($false),
% 5.04/5.26      inference('sat_resolution*', [status(thm)],
% 5.04/5.26                ['1', '27', '28', '53', '54', '70'])).
% 5.04/5.26  
% 5.04/5.26  % SZS output end Refutation
% 5.04/5.26  
% 5.04/5.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
