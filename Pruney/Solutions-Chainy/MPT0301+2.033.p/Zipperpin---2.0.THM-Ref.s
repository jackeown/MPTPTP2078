%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ihv5g1clrC

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 279 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  994 (2388 expanded)
%              Number of equality atoms :  148 ( 406 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X23: $i,X24: $i,X27: $i] :
      ( ( X27
        = ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X27 @ X23 @ X24 ) @ ( sk_E @ X27 @ X23 @ X24 ) @ ( sk_D @ X27 @ X23 @ X24 ) @ X23 @ X24 )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 @ X24 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X17 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 @ X18 ) ) ),
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
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('16',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('24',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,(
    ! [X23: $i,X24: $i,X27: $i] :
      ( ( X27
        = ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X27 @ X23 @ X24 ) @ ( sk_E @ X27 @ X23 @ X24 ) @ ( sk_D @ X27 @ X23 @ X24 ) @ X23 @ X24 )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 @ X24 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X22 @ X25 )
      | ( X25
       != ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
        | ( X0
          = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X34 ) )
      | ~ ( r2_hidden @ X32 @ X34 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        | ( X1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 = k1_xboole_0 )
        | ( X1 = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','58'])).

thf('60',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('62',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','61'])).

thf('63',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['59','63'])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('66',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X27: $i] :
      ( ( X27
        = ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X27 @ X23 @ X24 ) @ ( sk_E @ X27 @ X23 @ X24 ) @ ( sk_D @ X27 @ X23 @ X24 ) @ X23 @ X24 )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 @ X24 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X14 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('80',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_A )
        | ~ ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_A )
        = X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('91',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('93',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','25','26','67','68','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ihv5g1clrC
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 1066 iterations in 0.322s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.58/0.78  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.58/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(t113_zfmisc_1, conjecture,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i,B:$i]:
% 0.58/0.78        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.78          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      ((((sk_B_1) != (k1_xboole_0))
% 0.58/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.58/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf(d2_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.78           ( ?[E:$i,F:$i]:
% 0.58/0.78             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.58/0.78               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.58/0.78  thf(zf_stmt_2, axiom,
% 0.58/0.78    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.58/0.78     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.58/0.78       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.58/0.78         ( r2_hidden @ E @ A ) ) ))).
% 0.58/0.78  thf(zf_stmt_3, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.78           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i, X27 : $i]:
% 0.58/0.78         (((X27) = (k2_zfmisc_1 @ X24 @ X23))
% 0.58/0.78          | (zip_tseitin_0 @ (sk_F @ X27 @ X23 @ X24) @ 
% 0.58/0.78             (sk_E @ X27 @ X23 @ X24) @ (sk_D @ X27 @ X23 @ X24) @ X23 @ X24)
% 0.58/0.78          | (r2_hidden @ (sk_D @ X27 @ X23 @ X24) @ X27))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.78         ((r2_hidden @ X15 @ X17)
% 0.58/0.78          | ~ (zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.58/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.58/0.78          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.78  thf(t2_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.78  thf('5', plain,
% 0.58/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.78  thf(t4_xboole_0, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.78            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.58/0.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.78  thf('7', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.78  thf(t3_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.78  thf('8', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf(t79_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.58/0.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.78  thf('10', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.78  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.78      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.78  thf('12', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.58/0.78          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['4', '11'])).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      ((((sk_B_1) = (k1_xboole_0))
% 0.58/0.78        | ((sk_A) = (k1_xboole_0))
% 0.58/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.78      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.58/0.78         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.58/0.78         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['12', '16'])).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.58/0.78         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      ((((sk_A) != (k1_xboole_0))
% 0.58/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['20'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      ((((sk_B_1) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.58/0.78             (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '21'])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      ((((sk_B_1) != (sk_B_1)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.58/0.78             (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['22', '23'])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.58/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.58/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('split', [status(esa)], ['20'])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i, X27 : $i]:
% 0.58/0.78         (((X27) = (k2_zfmisc_1 @ X24 @ X23))
% 0.58/0.78          | (zip_tseitin_0 @ (sk_F @ X27 @ X23 @ X24) @ 
% 0.58/0.78             (sk_E @ X27 @ X23 @ X24) @ (sk_D @ X27 @ X23 @ X24) @ X23 @ X24)
% 0.58/0.78          | (r2_hidden @ (sk_D @ X27 @ X23 @ X24) @ X27))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.78         (~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.58/0.78          | (r2_hidden @ X22 @ X25)
% 0.58/0.78          | ((X25) != (k2_zfmisc_1 @ X24 @ X23)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.78         ((r2_hidden @ X22 @ (k2_zfmisc_1 @ X24 @ X23))
% 0.58/0.78          | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.58/0.78      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.58/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.58/0.78          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['29', '31'])).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0)
% 0.58/0.78           | ((X0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.58/0.78           | (r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['28', '32'])).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0)
% 0.58/0.78           | ((X0) = (k1_xboole_0))
% 0.58/0.78           | (r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['33', '34'])).
% 0.58/0.78  thf('36', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.78      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)
% 0.58/0.78           | ((X0) = (k1_xboole_0))))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('clc', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf(t7_xboole_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.78          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.78  thf('38', plain,
% 0.58/0.78      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.58/0.78      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.78  thf(l54_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.78     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.58/0.78       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.58/0.78         ((r2_hidden @ (k4_tarski @ X30 @ X32) @ (k2_zfmisc_1 @ X31 @ X34))
% 0.58/0.78          | ~ (r2_hidden @ X32 @ X34)
% 0.58/0.78          | ~ (r2_hidden @ X30 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (((X0) = (k1_xboole_0))
% 0.58/0.78          | ~ (r2_hidden @ X2 @ X1)
% 0.58/0.78          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.58/0.78             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      ((![X0 : $i, X1 : $i]:
% 0.58/0.78          (((X0) = (k1_xboole_0))
% 0.58/0.78           | (r2_hidden @ 
% 0.58/0.78              (k4_tarski @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (sk_B @ X1)) @ 
% 0.58/0.78              (k2_zfmisc_1 @ X0 @ X1))
% 0.58/0.78           | ((X1) = (k1_xboole_0))))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['37', '40'])).
% 0.58/0.78  thf('42', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf(t48_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.78  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['46', '47'])).
% 0.58/0.78  thf('49', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('50', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('demod', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain,
% 0.58/0.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.58/0.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.78  thf('53', plain,
% 0.58/0.78      ((![X0 : $i, X1 : $i]:
% 0.58/0.78          (((X0) = (k1_xboole_0))
% 0.58/0.78           | ((X1) = (k1_xboole_0))
% 0.58/0.78           | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['41', '52'])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      (((~ (r1_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.58/0.78         | ((sk_A) = (k1_xboole_0))
% 0.58/0.78         | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['27', '53'])).
% 0.58/0.78  thf('55', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.58/0.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.78  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.58/0.78      inference('sup+', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('59', plain,
% 0.58/0.78      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['54', '55', '58'])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('61', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.58/0.78       ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.78  thf('62', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['1', '61'])).
% 0.58/0.78  thf('63', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['60', '62'])).
% 0.58/0.78  thf('64', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['59', '63'])).
% 0.58/0.78  thf('65', plain,
% 0.58/0.78      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['20'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      ((((sk_A) != (sk_A)))
% 0.58/0.78         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.58/0.78             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) | 
% 0.58/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['66'])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) | 
% 0.58/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.58/0.78       (((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i, X27 : $i]:
% 0.58/0.78         (((X27) = (k2_zfmisc_1 @ X24 @ X23))
% 0.58/0.78          | (zip_tseitin_0 @ (sk_F @ X27 @ X23 @ X24) @ 
% 0.58/0.78             (sk_E @ X27 @ X23 @ X24) @ (sk_D @ X27 @ X23 @ X24) @ X23 @ X24)
% 0.58/0.78          | (r2_hidden @ (sk_D @ X27 @ X23 @ X24) @ X27))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.78  thf('70', plain,
% 0.58/0.78      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.78         ((r2_hidden @ X14 @ X18)
% 0.58/0.78          | ~ (zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.58/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.58/0.78          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.78  thf('72', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.58/0.78      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.78          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('75', plain,
% 0.58/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['74', '75'])).
% 0.58/0.78  thf('77', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('78', plain,
% 0.58/0.78      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (sk_A)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.58/0.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.78  thf('80', plain,
% 0.58/0.78      ((![X0 : $i, X1 : $i]:
% 0.58/0.78          (~ (r2_hidden @ X1 @ sk_A) | ~ (r1_xboole_0 @ X0 @ sk_A)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.78  thf('81', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('82', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_A) = (X0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['81', '82'])).
% 0.58/0.78  thf('84', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.58/0.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.78  thf('85', plain,
% 0.58/0.78      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['83', '84'])).
% 0.58/0.78  thf('86', plain,
% 0.58/0.78      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['80', '85'])).
% 0.58/0.78  thf('87', plain,
% 0.58/0.78      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['73', '86'])).
% 0.58/0.78  thf('88', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('89', plain,
% 0.58/0.78      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['87', '88'])).
% 0.58/0.78  thf('90', plain,
% 0.58/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['20'])).
% 0.58/0.78  thf('91', plain,
% 0.58/0.78      ((((sk_A) != (k1_xboole_0)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.58/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['89', '90'])).
% 0.58/0.78  thf('92', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['13'])).
% 0.58/0.78  thf('93', plain,
% 0.58/0.78      ((((sk_A) != (sk_A)))
% 0.58/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.58/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['91', '92'])).
% 0.58/0.78  thf('94', plain,
% 0.58/0.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.58/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['93'])).
% 0.58/0.78  thf('95', plain, ($false),
% 0.58/0.78      inference('sat_resolution*', [status(thm)],
% 0.58/0.78                ['1', '25', '26', '67', '68', '94'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
