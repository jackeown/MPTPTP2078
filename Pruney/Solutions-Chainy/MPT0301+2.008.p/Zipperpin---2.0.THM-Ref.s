%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1WLVeIjk9V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  712 (1339 expanded)
%              Number of equality atoms :  125 ( 276 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) )
      | ( r2_hidden @ ( sk_F @ X18 @ X17 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('47',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) )
      | ( r2_hidden @ ( sk_E @ X18 @ X17 @ X16 ) @ X16 )
      | ~ ( r2_hidden @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_A )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_A )
        | ~ ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('62',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('71',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','48','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1WLVeIjk9V
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 141 iterations in 0.062s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t113_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((((sk_B_1) != (k1_xboole_0))
% 0.21/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.51       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(t7_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('4', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf(t103_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.51          ( r2_hidden @ D @ A ) & 
% 0.21/0.51          ( ![E:$i,F:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.21/0.51                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X16 @ X17))
% 0.21/0.51          | (r2_hidden @ (sk_F @ X18 @ X17 @ X16) @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X18 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_F @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf(t2_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t4_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      ((![X0 : $i, X1 : $i]:
% 0.21/0.51          (~ (r2_hidden @ X1 @ sk_B_1) | ~ (r1_xboole_0 @ X0 @ sk_B_1)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.51  thf('17', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B_1))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_B_1))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (sk_B_1)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((((sk_A) != (k1_xboole_0))
% 0.21/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((sk_B_1) != (k1_xboole_0)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((((sk_B_1) != (sk_B_1)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.51       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.51       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf(l54_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.21/0.51          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.21/0.51             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.21/0.51             (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.51          | ((X1) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.51          k1_xboole_0)
% 0.21/0.51         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.51         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['30', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.51         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('clc', [status(thm)], ['36', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.51         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.51         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((sk_A) != (sk_A)))
% 0.21/0.51         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.21/0.51             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.51       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.51       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf('50', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X16 @ X17))
% 0.21/0.51          | (r2_hidden @ (sk_E @ X18 @ X17 @ X16) @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X18 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_E @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51             X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (sk_A)))
% 0.21/0.51         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((![X0 : $i, X1 : $i]:
% 0.21/0.51          (~ (r2_hidden @ X1 @ sk_A) | ~ (r1_xboole_0 @ X0 @ sk_A)))
% 0.21/0.51         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('62', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((![X1 : $i]: ~ (r2_hidden @ X1 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.21/0.51         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((sk_A) != (k1_xboole_0)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((((sk_A) != (sk_A)))
% 0.21/0.51         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.51             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.51       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.51       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.51       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('74', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['1', '28', '29', '48', '72', '73'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
