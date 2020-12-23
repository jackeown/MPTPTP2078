%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PkDyKYNdcK

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 169 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  803 (1515 expanded)
%              Number of equality atoms :  134 ( 289 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( X16
        = ( k2_zfmisc_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X16 @ X12 @ X13 ) @ ( sk_E @ X16 @ X12 @ X13 ) @ ( sk_D @ X16 @ X12 @ X13 ) @ X12 @ X13 )
      | ( r2_hidden @ ( sk_D @ X16 @ X12 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
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
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X19 ) )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

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
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
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
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X19 ) )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

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
    inference(split,[status(esa)],['10'])).

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
    inference(split,[status(esa)],['10'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X8 )
      | ~ ( r2_hidden @ X3 @ X8 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( X5
       != ( k4_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X3 @ X8 )
      | ( zip_tseitin_0 @ X4 @ X3 @ ( k4_tarski @ X3 @ X4 ) @ X6 @ X8 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ k1_xboole_0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ X1 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('43',plain,
    ( ( ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('48',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( X16
        = ( k2_zfmisc_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X16 @ X12 @ X13 ) @ ( sk_E @ X16 @ X12 @ X13 ) @ ( sk_D @ X16 @ X12 @ X13 ) @ X12 @ X13 )
      | ( r2_hidden @ ( sk_D @ X16 @ X12 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X3 @ X7 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X19 ) )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

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
    inference(split,[status(esa)],['10'])).

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

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','49','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PkDyKYNdcK
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 133 iterations in 0.078s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.35/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.52  thf(t113_zfmisc_1, conjecture,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i]:
% 0.35/0.52        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.52          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      ((((sk_B) != (k1_xboole_0))
% 0.35/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.35/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('split', [status(esa)], ['0'])).
% 0.35/0.52  thf(d2_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.52       ( ![D:$i]:
% 0.35/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.52           ( ?[E:$i,F:$i]:
% 0.35/0.52             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.35/0.52               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.35/0.52  thf(zf_stmt_2, axiom,
% 0.35/0.52    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.35/0.52     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.35/0.52       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.35/0.52         ( r2_hidden @ E @ A ) ) ))).
% 0.35/0.52  thf(zf_stmt_3, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.52       ( ![D:$i]:
% 0.35/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.52           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.35/0.52         (((X16) = (k2_zfmisc_1 @ X13 @ X12))
% 0.35/0.52          | (zip_tseitin_0 @ (sk_F @ X16 @ X12 @ X13) @ 
% 0.35/0.52             (sk_E @ X16 @ X12 @ X13) @ (sk_D @ X16 @ X12 @ X13) @ X12 @ X13)
% 0.35/0.52          | (r2_hidden @ (sk_D @ X16 @ X12 @ X13) @ X16))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.52         ((r2_hidden @ X4 @ X6) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.52          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.52          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf(t4_boole, axiom,
% 0.35/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.52  thf(t65_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X19 : $i, X20 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.35/0.52          | ((k4_xboole_0 @ X20 @ (k1_tarski @ X19)) != (X20)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.35/0.52          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['4', '8'])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      ((((sk_B) = (k1_xboole_0))
% 0.35/0.52        | ((sk_A) = (k1_xboole_0))
% 0.35/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))
% 0.35/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.35/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X19 : $i, X20 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.35/0.52          | ((k4_xboole_0 @ X20 @ (k1_tarski @ X19)) != (X20)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      ((![X0 : $i]: (((sk_B) != (sk_B)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.35/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.52  thf('19', plain,
% 0.35/0.52      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.35/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['9', '18'])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.35/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      ((((sk_A) != (k1_xboole_0))
% 0.35/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['22'])).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      ((((sk_B) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['21', '23'])).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      ((((sk_B) != (sk_B)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.52  thf('27', plain,
% 0.35/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.35/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.35/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('split', [status(esa)], ['22'])).
% 0.35/0.52  thf('29', plain,
% 0.35/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.35/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf(t2_tarski, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.35/0.52       ( ( A ) = ( B ) ) ))).
% 0.35/0.52  thf('30', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((X1) = (X0))
% 0.35/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.35/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.35/0.52  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.52  thf('34', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.35/0.52         ((zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X8)
% 0.35/0.52          | ~ (r2_hidden @ X3 @ X8)
% 0.35/0.52          | ~ (r2_hidden @ X4 @ X6)
% 0.35/0.52          | ((X5) != (k4_tarski @ X3 @ X4)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.52  thf('35', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X6 : $i, X8 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X4 @ X6)
% 0.35/0.52          | ~ (r2_hidden @ X3 @ X8)
% 0.35/0.52          | (zip_tseitin_0 @ X4 @ X3 @ (k4_tarski @ X3 @ X4) @ X6 @ X8))),
% 0.35/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.35/0.52  thf('36', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (X0))
% 0.35/0.52          | (zip_tseitin_0 @ (sk_C @ X0 @ k1_xboole_0) @ X2 @ 
% 0.35/0.52             (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ X0 @ X1)
% 0.35/0.52          | ~ (r2_hidden @ X2 @ X1))),
% 0.35/0.52      inference('sup-', [status(thm)], ['33', '35'])).
% 0.35/0.52  thf('37', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (X0))
% 0.35/0.52          | (zip_tseitin_0 @ (sk_C @ X1 @ k1_xboole_0) @ 
% 0.35/0.52             (sk_C @ X0 @ k1_xboole_0) @ 
% 0.35/0.52             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_C @ X1 @ k1_xboole_0)) @ 
% 0.35/0.52             X1 @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['32', '36'])).
% 0.35/0.52  thf('38', plain,
% 0.35/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.52         (~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.35/0.52          | (r2_hidden @ X11 @ X14)
% 0.35/0.52          | ((X14) != (k2_zfmisc_1 @ X13 @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.52  thf('39', plain,
% 0.35/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.52         ((r2_hidden @ X11 @ (k2_zfmisc_1 @ X13 @ X12))
% 0.35/0.52          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13))),
% 0.35/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.35/0.52  thf('40', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_xboole_0) = (X1))
% 0.35/0.52          | ((k1_xboole_0) = (X0))
% 0.35/0.52          | (r2_hidden @ 
% 0.35/0.52             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_C @ X1 @ k1_xboole_0)) @ 
% 0.35/0.52             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['37', '39'])).
% 0.35/0.52  thf('41', plain,
% 0.35/0.52      ((((r2_hidden @ 
% 0.35/0.52          (k4_tarski @ (sk_C @ sk_A @ k1_xboole_0) @ 
% 0.35/0.52           (sk_C @ sk_B @ k1_xboole_0)) @ 
% 0.35/0.52          k1_xboole_0)
% 0.35/0.52         | ((k1_xboole_0) = (sk_A))
% 0.35/0.52         | ((k1_xboole_0) = (sk_B))))
% 0.35/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup+', [status(thm)], ['29', '40'])).
% 0.35/0.52  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.52  thf('43', plain,
% 0.35/0.52      (((((k1_xboole_0) = (sk_B)) | ((k1_xboole_0) = (sk_A))))
% 0.35/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.35/0.52  thf('44', plain,
% 0.35/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['0'])).
% 0.35/0.52  thf('45', plain,
% 0.35/0.52      (((((sk_B) != (sk_B)) | ((k1_xboole_0) = (sk_A))))
% 0.35/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.52  thf('46', plain,
% 0.35/0.52      ((((k1_xboole_0) = (sk_A)))
% 0.35/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.35/0.52  thf('47', plain,
% 0.35/0.52      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['22'])).
% 0.35/0.52  thf('48', plain,
% 0.35/0.52      ((((sk_A) != (sk_A)))
% 0.35/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.35/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.52  thf('49', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) | 
% 0.35/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.35/0.52       (((sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.35/0.52  thf('50', plain,
% 0.35/0.52      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.35/0.52         (((X16) = (k2_zfmisc_1 @ X13 @ X12))
% 0.35/0.52          | (zip_tseitin_0 @ (sk_F @ X16 @ X12 @ X13) @ 
% 0.35/0.52             (sk_E @ X16 @ X12 @ X13) @ (sk_D @ X16 @ X12 @ X13) @ X12 @ X13)
% 0.35/0.52          | (r2_hidden @ (sk_D @ X16 @ X12 @ X13) @ X16))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.52  thf('51', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.52         ((r2_hidden @ X3 @ X7) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.52  thf('52', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.52          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.52          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.52  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.52  thf('54', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.35/0.52          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.35/0.52  thf('55', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('56', plain,
% 0.35/0.52      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.52  thf('57', plain,
% 0.35/0.52      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.35/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup+', [status(thm)], ['55', '56'])).
% 0.35/0.52  thf('58', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('59', plain,
% 0.35/0.52      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.35/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.35/0.52  thf('60', plain,
% 0.35/0.52      (![X19 : $i, X20 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.35/0.52          | ((k4_xboole_0 @ X20 @ (k1_tarski @ X19)) != (X20)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.52  thf('61', plain,
% 0.35/0.52      ((![X0 : $i]: (((sk_A) != (sk_A)) | ~ (r2_hidden @ X0 @ sk_A)))
% 0.35/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.52  thf('62', plain,
% 0.35/0.52      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['61'])).
% 0.35/0.52  thf('63', plain,
% 0.35/0.52      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['54', '62'])).
% 0.35/0.52  thf('64', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('65', plain,
% 0.35/0.52      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.35/0.52  thf('66', plain,
% 0.35/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['22'])).
% 0.35/0.52  thf('67', plain,
% 0.35/0.52      ((((sk_A) != (k1_xboole_0)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.52  thf('68', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('69', plain,
% 0.35/0.52      ((((sk_A) != (sk_A)))
% 0.35/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.35/0.52             (((sk_A) = (k1_xboole_0))))),
% 0.35/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.35/0.52  thf('70', plain,
% 0.35/0.52      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.35/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.35/0.52  thf('71', plain,
% 0.35/0.52      ((((sk_A) = (k1_xboole_0))) | 
% 0.35/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.35/0.52       (((sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('split', [status(esa)], ['10'])).
% 0.35/0.52  thf('72', plain, ($false),
% 0.35/0.52      inference('sat_resolution*', [status(thm)],
% 0.35/0.52                ['1', '27', '28', '49', '70', '71'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
