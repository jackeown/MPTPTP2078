%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.92yJfwCDoc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 305 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  929 (2769 expanded)
%              Number of equality atoms :  135 ( 415 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('30',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X19 @ X15 @ X16 ) @ ( sk_E @ X19 @ X15 @ X16 ) @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X6 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X3 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','58'])).

thf('60',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','61'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('68',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('73',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_A )
        | ~ ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('80',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('81',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('89',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','69','70','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.92yJfwCDoc
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 174 iterations in 0.111s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.57  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.57  thf(t113_zfmisc_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i]:
% 0.20/0.57        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.57          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((((sk_B) != (k1_xboole_0))
% 0.20/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.20/0.57       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf(d2_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57           ( ?[E:$i,F:$i]:
% 0.20/0.57             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.57               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.57  thf(zf_stmt_2, axiom,
% 0.20/0.57    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.57     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.57       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.57         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.57  thf(zf_stmt_3, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.20/0.57         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 0.20/0.57          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 0.20/0.57             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 0.20/0.57          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.57         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.20/0.57          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.57  thf(t2_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf(t4_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.57          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.57  thf('8', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.57  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))
% 0.20/0.57        | ((sk_A) = (k1_xboole_0))
% 0.20/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))
% 0.20/0.57         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))
% 0.20/0.57         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.57          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      ((![X0 : $i, X1 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X1 @ sk_B) | ~ (r1_xboole_0 @ X0 @ sk_B)))
% 0.20/0.57         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('20', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.20/0.57         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['10', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.20/0.57         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((((sk_A) != (k1_xboole_0))
% 0.20/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      ((((sk_B) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.57             (((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      ((((sk_B) != (sk_B)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.57             (((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.20/0.57       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.57       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('split', [status(esa)], ['26'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.57         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.20/0.57         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 0.20/0.57          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 0.20/0.57             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 0.20/0.57          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.57         ((r2_hidden @ X6 @ X10) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.20/0.57          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('37', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.20/0.57          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((X1) = (k1_xboole_0))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['38', '43'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.20/0.57          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.57  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.57  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((X1) = (k1_xboole_0))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.57         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 0.20/0.57          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.57          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.57          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X7 @ X9)
% 0.20/0.57          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.57          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 0.20/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (((X0) = (k1_xboole_0))
% 0.20/0.57          | (zip_tseitin_0 @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X3 @ 
% 0.20/0.57             (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ X0 @ X2)
% 0.20/0.57          | ~ (r2_hidden @ X3 @ X2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (((X0) = (k1_xboole_0))
% 0.20/0.57          | (zip_tseitin_0 @ (sk_D @ X2 @ k1_xboole_0 @ X3) @ 
% 0.20/0.57             (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 0.20/0.57             (k4_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 0.20/0.57              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.20/0.57             X2 @ X0)
% 0.20/0.57          | ((X2) = (k1_xboole_0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '54'])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.57          | (r2_hidden @ X14 @ X17)
% 0.20/0.57          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 0.20/0.57          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.20/0.57      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (((X1) = (k1_xboole_0))
% 0.20/0.57          | ((X0) = (k1_xboole_0))
% 0.20/0.57          | (r2_hidden @ 
% 0.20/0.57             (k4_tarski @ (sk_D @ X0 @ X3 @ k1_xboole_0) @ 
% 0.20/0.57              (sk_D @ X1 @ k1_xboole_0 @ X2)) @ 
% 0.20/0.57             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      ((![X0 : $i, X1 : $i]:
% 0.20/0.57          ((r2_hidden @ 
% 0.20/0.57            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.20/0.57             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.20/0.57            k1_xboole_0)
% 0.20/0.57           | ((sk_A) = (k1_xboole_0))
% 0.20/0.57           | ((sk_B) = (k1_xboole_0))))
% 0.20/0.57         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['33', '58'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.57       ~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.57  thf('62', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['1', '61'])).
% 0.20/0.57  thf('63', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['60', '62'])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      ((![X0 : $i, X1 : $i]:
% 0.20/0.57          ((r2_hidden @ 
% 0.20/0.57            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.20/0.57             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.20/0.57            k1_xboole_0)
% 0.20/0.57           | ((sk_A) = (k1_xboole_0))))
% 0.20/0.57         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['59', '63'])).
% 0.20/0.57  thf('65', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.57         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['26'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      ((((sk_A) != (sk_A)))
% 0.20/0.57         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.20/0.57             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) | 
% 0.20/0.57       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) | 
% 0.20/0.57       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.57       (((sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (sk_A)))
% 0.20/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.57          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      ((![X0 : $i, X1 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X1 @ sk_A) | ~ (r1_xboole_0 @ X0 @ sk_A)))
% 0.20/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('80', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['79', '80'])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['78', '81'])).
% 0.20/0.57  thf('83', plain,
% 0.20/0.57      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['71', '82'])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['83', '84'])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['26'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      ((((sk_A) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.57             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['11'])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      ((((sk_A) != (sk_A)))
% 0.20/0.57         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.57             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.57       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.20/0.57  thf('91', plain, ($false),
% 0.20/0.57      inference('sat_resolution*', [status(thm)],
% 0.20/0.57                ['1', '31', '32', '69', '70', '90'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
