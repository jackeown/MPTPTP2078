%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y0BgO2fxRc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:02 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 284 expanded)
%              Number of leaves         :   22 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  721 (2560 expanded)
%              Number of equality atoms :  108 ( 364 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('15',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('23',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('47',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X11 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
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
    inference('sup-',[status(thm)],['7','9'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('57',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('64',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','48','49','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y0BgO2fxRc
% 0.17/0.37  % Computer   : n021.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 20:56:20 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 402 iterations in 0.216s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.70  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.52/0.70  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(t113_zfmisc_1, conjecture,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i,B:$i]:
% 0.52/0.70        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.70          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.70  thf('0', plain,
% 0.52/0.70      ((((sk_B) != (k1_xboole_0))
% 0.52/0.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.52/0.70       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('split', [status(esa)], ['0'])).
% 0.52/0.70  thf(d2_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.52/0.70       ( ![D:$i]:
% 0.52/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.70           ( ?[E:$i,F:$i]:
% 0.52/0.70             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.52/0.70               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.52/0.70  thf(zf_stmt_2, axiom,
% 0.52/0.70    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.52/0.70     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.52/0.70       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.52/0.70         ( r2_hidden @ E @ A ) ) ))).
% 0.52/0.70  thf(zf_stmt_3, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.52/0.70       ( ![D:$i]:
% 0.52/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.70           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.52/0.70         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.52/0.70          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.52/0.70             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.52/0.70          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.70         ((r2_hidden @ X12 @ X14)
% 0.52/0.70          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.52/0.70          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.70          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.70  thf(t36_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.52/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.70  thf(l32_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (![X0 : $i, X2 : $i]:
% 0.52/0.70         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.70  thf(t64_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.52/0.70       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.52/0.70         (((X32) != (X34))
% 0.52/0.70          | ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34))))),
% 0.52/0.70      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      (![X33 : $i, X34 : $i]:
% 0.52/0.70         ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.70  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.70          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['4', '10'])).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      ((((sk_B) = (k1_xboole_0))
% 0.52/0.70        | ((sk_A) = (k1_xboole_0))
% 0.52/0.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70         <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['11', '15'])).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70         <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      ((((sk_A) != (k1_xboole_0))
% 0.52/0.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['19'])).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      ((((sk_B) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.52/0.70             (((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['18', '20'])).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      ((((sk_B) != (sk_B)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.52/0.70             (((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.52/0.70       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('split', [status(esa)], ['19'])).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.52/0.70         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.52/0.70          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.70          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.70  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.52/0.70          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.70          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['4', '10'])).
% 0.52/0.70  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((X1) = (k1_xboole_0))
% 0.52/0.70          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.52/0.70      inference('demod', [status(thm)], ['29', '32'])).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((X1) = (k1_xboole_0))
% 0.52/0.70          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.52/0.70      inference('demod', [status(thm)], ['29', '32'])).
% 0.52/0.70  thf(l54_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.70     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.52/0.70       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.52/0.70         ((r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X31))
% 0.52/0.70          | ~ (r2_hidden @ X29 @ X31)
% 0.52/0.70          | ~ (r2_hidden @ X27 @ X28))),
% 0.52/0.70      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.70         (((X0) = (k1_xboole_0))
% 0.52/0.70          | ~ (r2_hidden @ X3 @ X2)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 0.52/0.70             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.70         (((X0) = (k1_xboole_0))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 0.52/0.70              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.52/0.70             (k2_zfmisc_1 @ X0 @ X2))
% 0.52/0.70          | ((X2) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['33', '36'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      ((![X0 : $i, X1 : $i]:
% 0.52/0.70          ((r2_hidden @ 
% 0.52/0.70            (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 0.52/0.70             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.52/0.70            k1_xboole_0)
% 0.52/0.70           | ((sk_B) = (k1_xboole_0))
% 0.52/0.70           | ((sk_A) = (k1_xboole_0))))
% 0.52/0.70         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup+', [status(thm)], ['26', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['0'])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.52/0.70       ~ (((sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.70  thf('41', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['1', '40'])).
% 0.52/0.70  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      ((![X0 : $i, X1 : $i]:
% 0.52/0.70          ((r2_hidden @ 
% 0.52/0.70            (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 0.52/0.70             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.52/0.70            k1_xboole_0)
% 0.52/0.70           | ((sk_A) = (k1_xboole_0))))
% 0.52/0.70         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('simplify_reflect-', [status(thm)], ['38', '42'])).
% 0.52/0.70  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0)))
% 0.52/0.70         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('clc', [status(thm)], ['43', '44'])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['19'])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      ((((sk_A) != (sk_A)))
% 0.52/0.70         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.52/0.70             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.70  thf('48', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.70  thf('49', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.52/0.70       (((sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.52/0.70         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.52/0.70          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.52/0.70             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.52/0.70          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('51', plain,
% 0.52/0.70      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.70         ((r2_hidden @ X11 @ X15)
% 0.52/0.70          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.52/0.70          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.70          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.70  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.52/0.70          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.70  thf('57', plain,
% 0.52/0.70      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['54', '57'])).
% 0.52/0.70  thf('59', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('60', plain,
% 0.52/0.70      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['58', '59'])).
% 0.52/0.70  thf('61', plain,
% 0.52/0.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['19'])).
% 0.52/0.70  thf('62', plain,
% 0.52/0.70      ((((sk_A) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.52/0.70             (((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.52/0.70  thf('63', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['12'])).
% 0.52/0.70  thf('64', plain,
% 0.52/0.70      ((((sk_A) != (sk_A)))
% 0.52/0.70         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.52/0.70             (((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.70  thf('65', plain,
% 0.52/0.70      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['64'])).
% 0.52/0.70  thf('66', plain, ($false),
% 0.52/0.70      inference('sat_resolution*', [status(thm)],
% 0.52/0.70                ['1', '24', '25', '48', '49', '65'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
