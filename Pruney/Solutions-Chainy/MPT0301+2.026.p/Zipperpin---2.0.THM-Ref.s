%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBLEGmLUnW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:02 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  676 (1227 expanded)
%              Number of equality atoms :  107 ( 218 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('22',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,
    ( ( ( k1_xboole_0 = sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('40',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( X16
        = ( k2_zfmisc_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X16 @ X12 @ X13 ) @ ( sk_E @ X16 @ X12 @ X13 ) @ ( sk_D @ X16 @ X12 @ X13 ) @ X12 @ X13 )
      | ( r2_hidden @ ( sk_D @ X16 @ X12 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X3 @ X7 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('48',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('56',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('58',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','41','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBLEGmLUnW
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:20:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 292 iterations in 0.236s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.50/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.68  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.50/0.68  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.50/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.68  thf(t113_zfmisc_1, conjecture,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i]:
% 0.50/0.68        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.68          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.68  thf('0', plain,
% 0.50/0.68      ((((sk_B) != (k1_xboole_0))
% 0.50/0.68        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.50/0.68       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('split', [status(esa)], ['0'])).
% 0.50/0.68  thf(d2_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.50/0.68       ( ![D:$i]:
% 0.50/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.68           ( ?[E:$i,F:$i]:
% 0.50/0.68             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.50/0.68               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.50/0.68  thf(zf_stmt_2, axiom,
% 0.50/0.68    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.50/0.68     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.50/0.68       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.50/0.68         ( r2_hidden @ E @ A ) ) ))).
% 0.50/0.68  thf(zf_stmt_3, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.50/0.68       ( ![D:$i]:
% 0.50/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.68           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.50/0.68         (((X16) = (k2_zfmisc_1 @ X13 @ X12))
% 0.50/0.68          | (zip_tseitin_0 @ (sk_F @ X16 @ X12 @ X13) @ 
% 0.50/0.68             (sk_E @ X16 @ X12 @ X13) @ (sk_D @ X16 @ X12 @ X13) @ X12 @ X13)
% 0.50/0.68          | (r2_hidden @ (sk_D @ X16 @ X12 @ X13) @ X16))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((r2_hidden @ X4 @ X6) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.50/0.68          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.50/0.68          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.50/0.68  thf('5', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.50/0.68  thf(l24_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i]:
% 0.50/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.50/0.68      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.50/0.68  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('8', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.50/0.68          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['4', '7'])).
% 0.50/0.68  thf('9', plain,
% 0.50/0.68      ((((sk_B) = (k1_xboole_0))
% 0.50/0.68        | ((sk_A) = (k1_xboole_0))
% 0.50/0.68        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('11', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.50/0.68  thf('12', plain,
% 0.50/0.68      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i]:
% 0.50/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.50/0.68      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.50/0.68  thf('14', plain,
% 0.50/0.68      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.50/0.68         <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['8', '14'])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.50/0.68         <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('demod', [status(thm)], ['15', '16'])).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      ((((sk_A) != (k1_xboole_0))
% 0.50/0.68        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['18'])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      ((((sk_B) != (k1_xboole_0)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['17', '19'])).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      ((((sk_B) != (sk_B)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.50/0.68       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.50/0.68       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('split', [status(esa)], ['18'])).
% 0.50/0.68  thf('25', plain,
% 0.50/0.68      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.50/0.68         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf(t2_tarski, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.50/0.68       ( ( A ) = ( B ) ) ))).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((X1) = (X0))
% 0.50/0.68          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.50/0.68          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_tarski])).
% 0.50/0.68  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('28', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.68  thf('29', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.68  thf(l54_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.50/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.50/0.68  thf('30', plain,
% 0.50/0.68      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.50/0.68         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.50/0.68          | ~ (r2_hidden @ X23 @ X25)
% 0.50/0.68          | ~ (r2_hidden @ X21 @ X22))),
% 0.50/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (((k1_xboole_0) = (X0))
% 0.50/0.68          | ~ (r2_hidden @ X2 @ X1)
% 0.50/0.68          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 0.50/0.68             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((k1_xboole_0) = (X0))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_C @ X1 @ k1_xboole_0)) @ 
% 0.50/0.68             (k2_zfmisc_1 @ X0 @ X1))
% 0.50/0.68          | ((k1_xboole_0) = (X1)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['28', '31'])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      ((((r2_hidden @ 
% 0.50/0.68          (k4_tarski @ (sk_C @ sk_A @ k1_xboole_0) @ 
% 0.50/0.68           (sk_C @ sk_B @ k1_xboole_0)) @ 
% 0.50/0.68          k1_xboole_0)
% 0.50/0.68         | ((k1_xboole_0) = (sk_B))
% 0.50/0.68         | ((k1_xboole_0) = (sk_A))))
% 0.50/0.68         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['25', '32'])).
% 0.50/0.68  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('35', plain,
% 0.50/0.68      (((((k1_xboole_0) = (sk_A)) | ((k1_xboole_0) = (sk_B))))
% 0.50/0.68         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['0'])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (((((sk_B) != (sk_B)) | ((k1_xboole_0) = (sk_A))))
% 0.50/0.68         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.68  thf('38', plain,
% 0.50/0.68      ((((k1_xboole_0) = (sk_A)))
% 0.50/0.68         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.50/0.68  thf('39', plain,
% 0.50/0.68      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['18'])).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      ((((sk_A) != (sk_A)))
% 0.50/0.68         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.50/0.68             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.68  thf('41', plain,
% 0.50/0.68      ((((sk_A) = (k1_xboole_0))) | 
% 0.50/0.68       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.50/0.68       (((sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['40'])).
% 0.50/0.68  thf('42', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.50/0.68         (((X16) = (k2_zfmisc_1 @ X13 @ X12))
% 0.50/0.68          | (zip_tseitin_0 @ (sk_F @ X16 @ X12 @ X13) @ 
% 0.50/0.68             (sk_E @ X16 @ X12 @ X13) @ (sk_D @ X16 @ X12 @ X13) @ X12 @ X13)
% 0.50/0.68          | (r2_hidden @ (sk_D @ X16 @ X12 @ X13) @ X16))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((r2_hidden @ X3 @ X7) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.50/0.68          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.50/0.68          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.68  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('46', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.50/0.68          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.50/0.68  thf('47', plain,
% 0.50/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('48', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.50/0.68  thf('49', plain,
% 0.50/0.68      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['47', '48'])).
% 0.50/0.68  thf('50', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i]:
% 0.50/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.50/0.68      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.50/0.68  thf('51', plain,
% 0.50/0.68      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['46', '51'])).
% 0.50/0.68  thf('53', plain,
% 0.50/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('54', plain,
% 0.50/0.68      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.68  thf('55', plain,
% 0.50/0.68      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['18'])).
% 0.50/0.68  thf('56', plain,
% 0.50/0.68      ((((sk_A) != (k1_xboole_0)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.68  thf('57', plain,
% 0.50/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('58', plain,
% 0.50/0.68      ((((sk_A) != (sk_A)))
% 0.50/0.68         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.50/0.68             (((sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('demod', [status(thm)], ['56', '57'])).
% 0.50/0.68  thf('59', plain,
% 0.50/0.68      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.50/0.68       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['58'])).
% 0.50/0.68  thf('60', plain,
% 0.50/0.68      ((((sk_A) = (k1_xboole_0))) | 
% 0.50/0.68       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.50/0.68       (((sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('split', [status(esa)], ['9'])).
% 0.50/0.68  thf('61', plain, ($false),
% 0.50/0.68      inference('sat_resolution*', [status(thm)],
% 0.50/0.68                ['1', '23', '24', '41', '59', '60'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
