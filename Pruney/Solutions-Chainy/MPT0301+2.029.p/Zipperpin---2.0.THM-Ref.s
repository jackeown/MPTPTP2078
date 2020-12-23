%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HNb8FCMLtd

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 242 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  719 (1911 expanded)
%              Number of equality atoms :  110 ( 264 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
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

thf('8',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k5_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('24',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('32',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('43',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('48',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X9 @ X13 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('56',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','18'])).

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
    inference(split,[status(esa)],['21'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('64',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','49','65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HNb8FCMLtd
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.63  % Solved by: fo/fo7.sh
% 0.48/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.63  % done 349 iterations in 0.174s
% 0.48/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.63  % SZS output start Refutation
% 0.48/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.63  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.48/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.48/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.63  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.48/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.63  thf(t113_zfmisc_1, conjecture,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.63    (~( ![A:$i,B:$i]:
% 0.48/0.63        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.63          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.48/0.63    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.63  thf('0', plain,
% 0.48/0.63      ((((sk_B_1) != (k1_xboole_0))
% 0.48/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('1', plain,
% 0.48/0.63      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.48/0.63       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('split', [status(esa)], ['0'])).
% 0.48/0.63  thf(d2_zfmisc_1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i]:
% 0.48/0.63     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.48/0.63       ( ![D:$i]:
% 0.48/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.63           ( ?[E:$i,F:$i]:
% 0.48/0.63             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.48/0.63               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.48/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.48/0.63  thf(zf_stmt_2, axiom,
% 0.48/0.63    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.48/0.63     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.48/0.63       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.48/0.63         ( r2_hidden @ E @ A ) ) ))).
% 0.48/0.63  thf(zf_stmt_3, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i]:
% 0.48/0.63     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.48/0.63       ( ![D:$i]:
% 0.48/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.63           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.48/0.63  thf('2', plain,
% 0.48/0.63      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.48/0.63         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 0.48/0.63          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 0.48/0.63             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 0.48/0.63          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.63  thf('3', plain,
% 0.48/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.63         ((r2_hidden @ X10 @ X12)
% 0.48/0.63          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.63  thf('4', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.63         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.48/0.63          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.48/0.63          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.48/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.63  thf(t2_boole, axiom,
% 0.48/0.63    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.63  thf('5', plain,
% 0.48/0.63      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.63  thf(t4_xboole_0, axiom,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.63  thf('6', plain,
% 0.48/0.63      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.48/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.48/0.63          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.48/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.63  thf('7', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.63  thf('8', plain,
% 0.48/0.63      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.63  thf(l97_xboole_1, axiom,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.48/0.63  thf('9', plain,
% 0.48/0.63      (![X5 : $i, X6 : $i]:
% 0.48/0.63         (r1_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k5_xboole_0 @ X5 @ X6))),
% 0.48/0.63      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.48/0.63  thf('10', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.48/0.63  thf(t5_boole, axiom,
% 0.48/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.63  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.48/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.63  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.48/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.48/0.63  thf('13', plain,
% 0.48/0.63      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.63  thf('14', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((r1_xboole_0 @ X0 @ X1)
% 0.48/0.63          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.48/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.63  thf('15', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.48/0.63          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.48/0.63  thf('16', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.63  thf('17', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((r1_xboole_0 @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.63  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.48/0.63      inference('sup-', [status(thm)], ['12', '17'])).
% 0.48/0.63  thf('19', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.63      inference('demod', [status(thm)], ['7', '18'])).
% 0.48/0.63  thf('20', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.48/0.63          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['4', '19'])).
% 0.48/0.63  thf('21', plain,
% 0.48/0.63      ((((sk_B_1) = (k1_xboole_0))
% 0.48/0.63        | ((sk_A) = (k1_xboole_0))
% 0.48/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('22', plain,
% 0.48/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('23', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.63      inference('demod', [status(thm)], ['7', '18'])).
% 0.48/0.63  thf('24', plain,
% 0.48/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.48/0.63         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.63  thf('25', plain,
% 0.48/0.63      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.63         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['20', '24'])).
% 0.48/0.63  thf('26', plain,
% 0.48/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('27', plain,
% 0.48/0.63      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.63         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.48/0.63  thf('28', plain,
% 0.48/0.63      ((((sk_A) != (k1_xboole_0))
% 0.48/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('29', plain,
% 0.48/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['28'])).
% 0.48/0.63  thf('30', plain,
% 0.48/0.63      ((((sk_B_1) != (k1_xboole_0)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.48/0.63  thf('31', plain,
% 0.48/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('32', plain,
% 0.48/0.63      ((((sk_B_1) != (sk_B_1)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.48/0.63  thf('33', plain,
% 0.48/0.63      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.48/0.63       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.48/0.63  thf('34', plain,
% 0.48/0.63      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.48/0.63       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('split', [status(esa)], ['28'])).
% 0.48/0.63  thf('35', plain,
% 0.48/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.48/0.63         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf(t7_xboole_0, axiom,
% 0.48/0.63    (![A:$i]:
% 0.48/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.48/0.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.48/0.63  thf('36', plain,
% 0.48/0.63      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.48/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.48/0.63  thf('37', plain,
% 0.48/0.63      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.48/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.48/0.63  thf(l54_zfmisc_1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.63     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.48/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.48/0.63  thf('38', plain,
% 0.48/0.63      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.48/0.63         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X29))
% 0.48/0.63          | ~ (r2_hidden @ X27 @ X29)
% 0.48/0.63          | ~ (r2_hidden @ X25 @ X26))),
% 0.48/0.63      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.48/0.63  thf('39', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.63         (((X0) = (k1_xboole_0))
% 0.48/0.63          | ~ (r2_hidden @ X2 @ X1)
% 0.48/0.63          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.48/0.63             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.63  thf('40', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         (((X0) = (k1_xboole_0))
% 0.48/0.63          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.48/0.63             (k2_zfmisc_1 @ X0 @ X1))
% 0.48/0.63          | ((X1) = (k1_xboole_0)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['36', '39'])).
% 0.48/0.63  thf('41', plain,
% 0.48/0.63      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.48/0.63          k1_xboole_0)
% 0.48/0.63         | ((sk_B_1) = (k1_xboole_0))
% 0.48/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.48/0.63         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup+', [status(thm)], ['35', '40'])).
% 0.48/0.63  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.63      inference('demod', [status(thm)], ['7', '18'])).
% 0.48/0.63  thf('43', plain,
% 0.48/0.63      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.48/0.63         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('clc', [status(thm)], ['41', '42'])).
% 0.48/0.63  thf('44', plain,
% 0.48/0.63      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['0'])).
% 0.48/0.63  thf('45', plain,
% 0.48/0.63      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.48/0.63         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.63  thf('46', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0)))
% 0.48/0.63         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('simplify', [status(thm)], ['45'])).
% 0.48/0.63  thf('47', plain,
% 0.48/0.63      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['28'])).
% 0.48/0.63  thf('48', plain,
% 0.48/0.63      ((((sk_A) != (sk_A)))
% 0.48/0.63         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.48/0.63             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.63  thf('49', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0))) | 
% 0.48/0.63       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.48/0.63       (((sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.48/0.63  thf('50', plain,
% 0.48/0.63      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.48/0.63         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 0.48/0.63          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 0.48/0.63             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 0.48/0.63          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.63  thf('51', plain,
% 0.48/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.63         ((r2_hidden @ X9 @ X13)
% 0.48/0.63          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.63  thf('52', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.63         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.48/0.63          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.48/0.63          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.63  thf('53', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.63      inference('demod', [status(thm)], ['7', '18'])).
% 0.48/0.63  thf('54', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.48/0.63          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.48/0.63  thf('55', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('56', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.63      inference('demod', [status(thm)], ['7', '18'])).
% 0.48/0.63  thf('57', plain,
% 0.48/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.48/0.63  thf('58', plain,
% 0.48/0.63      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.48/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['54', '57'])).
% 0.48/0.63  thf('59', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('60', plain,
% 0.48/0.63      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.48/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.48/0.63  thf('61', plain,
% 0.48/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['28'])).
% 0.48/0.63  thf('62', plain,
% 0.48/0.63      ((((sk_A) != (k1_xboole_0)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.48/0.63  thf('63', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('64', plain,
% 0.48/0.63      ((((sk_A) != (sk_A)))
% 0.48/0.63         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.48/0.63             (((sk_A) = (k1_xboole_0))))),
% 0.48/0.63      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.63  thf('65', plain,
% 0.48/0.63      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.48/0.63       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['64'])).
% 0.48/0.63  thf('66', plain,
% 0.48/0.63      ((((sk_A) = (k1_xboole_0))) | 
% 0.48/0.63       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.48/0.63       (((sk_B_1) = (k1_xboole_0)))),
% 0.48/0.63      inference('split', [status(esa)], ['21'])).
% 0.48/0.63  thf('67', plain, ($false),
% 0.48/0.63      inference('sat_resolution*', [status(thm)],
% 0.48/0.63                ['1', '33', '34', '49', '65', '66'])).
% 0.48/0.63  
% 0.48/0.63  % SZS output end Refutation
% 0.48/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
