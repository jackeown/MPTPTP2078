%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uirL4MjSO2

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 389 expanded)
%              Number of leaves         :   26 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  810 (3067 expanded)
%              Number of equality atoms :  114 ( 390 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('20',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X11 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('47',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('62',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('67',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('68',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('75',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','63','64','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uirL4MjSO2
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 332 iterations in 0.203s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.46/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.46/0.65  thf(t113_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((((sk_B) != (k1_xboole_0))
% 0.46/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.46/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(d2_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ?[E:$i,F:$i]:
% 0.46/0.65             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.65               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_2, axiom,
% 0.46/0.65    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.46/0.65       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.65         ( r2_hidden @ E @ A ) ) ))).
% 0.46/0.65  thf(zf_stmt_3, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.46/0.65         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.46/0.65          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.46/0.65             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.46/0.65          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         ((r2_hidden @ X12 @ X14)
% 0.46/0.65          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.46/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.46/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf(t17_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.46/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.65  thf(t3_xboole_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf(t4_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.46/0.65          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf(t2_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf(l97_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf(t5_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('13', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      ((((sk_B) = (k1_xboole_0))
% 0.46/0.65        | ((sk_A) = (k1_xboole_0))
% 0.46/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('19', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((((sk_A) != (k1_xboole_0))
% 0.46/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((((sk_B) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.46/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      ((((sk_B) != (sk_B)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.46/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.46/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['24'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.46/0.65         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.46/0.65          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.46/0.65             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.46/0.65          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         ((r2_hidden @ X11 @ X15)
% 0.46/0.65          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.46/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.46/0.65          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.46/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.46/0.65          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X1) = (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.46/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.46/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('44', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '15'])).
% 0.46/0.65  thf('47', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X1) = (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '48'])).
% 0.46/0.65  thf(l54_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.46/0.65         ((r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X31))
% 0.46/0.65          | ~ (r2_hidden @ X29 @ X31)
% 0.46/0.65          | ~ (r2_hidden @ X27 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (((X0) = (k1_xboole_0))
% 0.46/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 0.46/0.65             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (((X0) = (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k4_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 0.46/0.65              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.46/0.65             (k2_zfmisc_1 @ X0 @ X2))
% 0.46/0.65          | ((X2) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['42', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((![X0 : $i, X1 : $i]:
% 0.46/0.65          ((r2_hidden @ 
% 0.46/0.65            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.46/0.65             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.46/0.65            k1_xboole_0)
% 0.46/0.65           | ((sk_B) = (k1_xboole_0))
% 0.46/0.65           | ((sk_A) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['31', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.65       ~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('56', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['1', '55'])).
% 0.46/0.65  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((![X0 : $i, X1 : $i]:
% 0.46/0.65          ((r2_hidden @ 
% 0.46/0.65            (k4_tarski @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ 
% 0.46/0.65             (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.46/0.65            k1_xboole_0)
% 0.46/0.65           | ((sk_A) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['53', '57'])).
% 0.46/0.65  thf('59', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['24'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      ((((sk_A) != (sk_A)))
% 0.46/0.65         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.46/0.65             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.46/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.46/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.65       (((sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.65          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('67', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.65         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['65', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.65         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['24'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((((sk_A) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.46/0.65             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['17'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      ((((sk_A) != (sk_A)))
% 0.46/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.46/0.65             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.65  thf('77', plain, ($false),
% 0.46/0.65      inference('sat_resolution*', [status(thm)],
% 0.46/0.65                ['1', '29', '30', '63', '64', '76'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
