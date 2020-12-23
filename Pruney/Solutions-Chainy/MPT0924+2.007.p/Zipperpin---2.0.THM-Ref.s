%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzRqyjv3fT

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:18 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 187 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  996 (2602 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t84_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( r2_hidden @ ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
    <=> ( ( r2_hidden @ A @ E )
        & ( r2_hidden @ B @ F )
        & ( r2_hidden @ C @ G )
        & ( r2_hidden @ D @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( r2_hidden @ ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
      <=> ( ( r2_hidden @ A @ E )
          & ( r2_hidden @ B @ F )
          & ( r2_hidden @ C @ G )
          & ( r2_hidden @ D @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_mcart_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ X5 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k3_mcart_1 @ X7 @ X6 @ X5 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_G )
   <= ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( r2_hidden @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) )
   <= ( r2_hidden @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_G ) ) )
   <= ( r2_hidden @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ sk_G ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X0 @ X4 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_H ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['16'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['32','37'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_H )
   <= ~ ( r2_hidden @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['16'])).

thf('49',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_F )
   <= ~ ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['16'])).

thf('60',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('63',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E )
   <= ~ ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['16'])).

thf('65',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['16'])).

thf('67',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['20'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','46','49','60','65','66','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzRqyjv3fT
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.19/1.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.44  % Solved by: fo/fo7.sh
% 1.19/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.44  % done 1107 iterations in 0.988s
% 1.19/1.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.44  % SZS output start Refutation
% 1.19/1.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.19/1.44  thf(sk_G_type, type, sk_G: $i).
% 1.19/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.19/1.44  thf(sk_D_type, type, sk_D: $i).
% 1.19/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.44  thf(sk_F_type, type, sk_F: $i).
% 1.19/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.44  thf(sk_H_type, type, sk_H: $i).
% 1.19/1.44  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.19/1.44  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.19/1.44  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.19/1.44  thf(sk_E_type, type, sk_E: $i).
% 1.19/1.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.44  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.19/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.44  thf(t84_mcart_1, conjecture,
% 1.19/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.19/1.44     ( ( r2_hidden @
% 1.19/1.44         ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 1.19/1.44       ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 1.19/1.44         ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ))).
% 1.19/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.44    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.19/1.44        ( ( r2_hidden @
% 1.19/1.44            ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 1.19/1.44          ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 1.19/1.44            ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ) )),
% 1.19/1.44    inference('cnf.neg', [status(esa)], [t84_mcart_1])).
% 1.19/1.44  thf('0', plain,
% 1.19/1.44      (((r2_hidden @ sk_C @ sk_G)
% 1.19/1.44        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.44  thf('1', plain,
% 1.19/1.44      (((r2_hidden @ sk_C @ sk_G)) | 
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('split', [status(esa)], ['0'])).
% 1.19/1.44  thf('2', plain,
% 1.19/1.44      (((r2_hidden @ sk_A @ sk_E)
% 1.19/1.44        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.44  thf('3', plain,
% 1.19/1.44      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('split', [status(esa)], ['2'])).
% 1.19/1.44  thf(d4_zfmisc_1, axiom,
% 1.19/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.44     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.19/1.44       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.19/1.44  thf('4', plain,
% 1.19/1.44      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.44         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 1.19/1.44           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.19/1.44  thf(d4_mcart_1, axiom,
% 1.19/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.44     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 1.19/1.44       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 1.19/1.44  thf('5', plain,
% 1.19/1.44      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.19/1.44         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 1.19/1.44           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_mcart_1])).
% 1.19/1.44  thf(t106_zfmisc_1, axiom,
% 1.19/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.44     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.19/1.44       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.19/1.44  thf('6', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X0 @ X1)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('7', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.19/1.44             (k2_zfmisc_1 @ X5 @ X4))
% 1.19/1.44          | (r2_hidden @ (k3_mcart_1 @ X3 @ X2 @ X1) @ X5))),
% 1.19/1.44      inference('sup-', [status(thm)], ['5', '6'])).
% 1.19/1.44  thf('8', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 1.19/1.44             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.44          | (r2_hidden @ (k3_mcart_1 @ X7 @ X6 @ X5) @ 
% 1.19/1.44             (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['4', '7'])).
% 1.19/1.44  thf('9', plain,
% 1.19/1.44      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 1.19/1.44         (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['3', '8'])).
% 1.19/1.44  thf(d3_zfmisc_1, axiom,
% 1.19/1.44    (![A:$i,B:$i,C:$i]:
% 1.19/1.44     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.19/1.44       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.19/1.44  thf('10', plain,
% 1.19/1.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.19/1.44         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 1.19/1.44           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.19/1.44  thf(d3_mcart_1, axiom,
% 1.19/1.44    (![A:$i,B:$i,C:$i]:
% 1.19/1.44     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.19/1.44  thf('11', plain,
% 1.19/1.44      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.19/1.44         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.19/1.44           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.19/1.44  thf('12', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X2 @ X3)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('13', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 1.19/1.44          | (r2_hidden @ X0 @ X3))),
% 1.19/1.44      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.44  thf('14', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k3_mcart_1 @ X5 @ X4 @ X3) @ 
% 1.19/1.44             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.19/1.44          | (r2_hidden @ X3 @ X0))),
% 1.19/1.44      inference('sup-', [status(thm)], ['10', '13'])).
% 1.19/1.44  thf('15', plain,
% 1.19/1.44      (((r2_hidden @ sk_C @ sk_G))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['9', '14'])).
% 1.19/1.44  thf('16', plain,
% 1.19/1.44      ((~ (r2_hidden @ sk_D @ sk_H)
% 1.19/1.44        | ~ (r2_hidden @ sk_C @ sk_G)
% 1.19/1.44        | ~ (r2_hidden @ sk_B @ sk_F)
% 1.19/1.44        | ~ (r2_hidden @ sk_A @ sk_E)
% 1.19/1.44        | ~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44             (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.44  thf('17', plain,
% 1.19/1.44      ((~ (r2_hidden @ sk_C @ sk_G)) <= (~ ((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('18', plain,
% 1.19/1.44      (~
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) | 
% 1.19/1.44       ((r2_hidden @ sk_C @ sk_G))),
% 1.19/1.44      inference('sup-', [status(thm)], ['15', '17'])).
% 1.19/1.44  thf('19', plain,
% 1.19/1.44      (((r2_hidden @ sk_A @ sk_E)) <= (((r2_hidden @ sk_A @ sk_E)))),
% 1.19/1.44      inference('split', [status(esa)], ['2'])).
% 1.19/1.44  thf('20', plain,
% 1.19/1.44      (((r2_hidden @ sk_B @ sk_F)
% 1.19/1.44        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.44  thf('21', plain,
% 1.19/1.44      (((r2_hidden @ sk_B @ sk_F)) <= (((r2_hidden @ sk_B @ sk_F)))),
% 1.19/1.44      inference('split', [status(esa)], ['20'])).
% 1.19/1.44  thf('22', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 1.19/1.44         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 1.19/1.44          | ~ (r2_hidden @ X2 @ X4)
% 1.19/1.44          | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('23', plain,
% 1.19/1.44      ((![X0 : $i, X1 : $i]:
% 1.19/1.44          (~ (r2_hidden @ X1 @ X0)
% 1.19/1.44           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_F))))
% 1.19/1.44         <= (((r2_hidden @ sk_B @ sk_F)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['21', '22'])).
% 1.19/1.44  thf('24', plain,
% 1.19/1.44      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F)))
% 1.19/1.44         <= (((r2_hidden @ sk_A @ sk_E)) & ((r2_hidden @ sk_B @ sk_F)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['19', '23'])).
% 1.19/1.44  thf('25', plain,
% 1.19/1.44      (((r2_hidden @ sk_C @ sk_G)) <= (((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('split', [status(esa)], ['0'])).
% 1.19/1.44  thf('26', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 1.19/1.44         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 1.19/1.44          | ~ (r2_hidden @ X2 @ X4)
% 1.19/1.44          | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('27', plain,
% 1.19/1.44      ((![X0 : $i, X1 : $i]:
% 1.19/1.44          (~ (r2_hidden @ X1 @ X0)
% 1.19/1.44           | (r2_hidden @ (k4_tarski @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_G))))
% 1.19/1.44         <= (((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['25', '26'])).
% 1.19/1.44  thf('28', plain,
% 1.19/1.44      (((r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.19/1.44         (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ sk_G)))
% 1.19/1.44         <= (((r2_hidden @ sk_A @ sk_E)) & 
% 1.19/1.44             ((r2_hidden @ sk_B @ sk_F)) & 
% 1.19/1.44             ((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['24', '27'])).
% 1.19/1.44  thf('29', plain,
% 1.19/1.44      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.19/1.44         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.19/1.44           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.19/1.44  thf('30', plain,
% 1.19/1.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.19/1.44         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 1.19/1.44           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.19/1.44  thf('31', plain,
% 1.19/1.44      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 1.19/1.44         (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))
% 1.19/1.44         <= (((r2_hidden @ sk_A @ sk_E)) & 
% 1.19/1.44             ((r2_hidden @ sk_B @ sk_F)) & 
% 1.19/1.44             ((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.19/1.44  thf('32', plain,
% 1.19/1.44      (((r2_hidden @ sk_D @ sk_H)
% 1.19/1.44        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.44  thf('33', plain,
% 1.19/1.44      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.44         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 1.19/1.44           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.19/1.44  thf('34', plain,
% 1.19/1.44      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.19/1.44         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 1.19/1.44           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_mcart_1])).
% 1.19/1.44  thf('35', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X2 @ X3)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('36', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.19/1.44             (k2_zfmisc_1 @ X5 @ X4))
% 1.19/1.44          | (r2_hidden @ X0 @ X4))),
% 1.19/1.44      inference('sup-', [status(thm)], ['34', '35'])).
% 1.19/1.44  thf('37', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 1.19/1.44             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.44          | (r2_hidden @ X4 @ X0))),
% 1.19/1.44      inference('sup-', [status(thm)], ['33', '36'])).
% 1.19/1.44  thf('38', plain, ((r2_hidden @ sk_D @ sk_H)),
% 1.19/1.44      inference('clc', [status(thm)], ['32', '37'])).
% 1.19/1.44  thf('39', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 1.19/1.44         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 1.19/1.44          | ~ (r2_hidden @ X2 @ X4)
% 1.19/1.44          | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('40', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i]:
% 1.19/1.44         (~ (r2_hidden @ X1 @ X0)
% 1.19/1.44          | (r2_hidden @ (k4_tarski @ X1 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_H)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.19/1.44  thf('41', plain,
% 1.19/1.44      (((r2_hidden @ (k4_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_D) @ 
% 1.19/1.44         (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H)))
% 1.19/1.44         <= (((r2_hidden @ sk_A @ sk_E)) & 
% 1.19/1.44             ((r2_hidden @ sk_B @ sk_F)) & 
% 1.19/1.44             ((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['31', '40'])).
% 1.19/1.44  thf('42', plain,
% 1.19/1.44      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.19/1.44         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 1.19/1.44           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_mcart_1])).
% 1.19/1.44  thf('43', plain,
% 1.19/1.44      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.44         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 1.19/1.44           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 1.19/1.44      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.19/1.44  thf('44', plain,
% 1.19/1.44      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 1.19/1.44         <= (((r2_hidden @ sk_A @ sk_E)) & 
% 1.19/1.44             ((r2_hidden @ sk_B @ sk_F)) & 
% 1.19/1.44             ((r2_hidden @ sk_C @ sk_G)))),
% 1.19/1.44      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.19/1.44  thf('45', plain,
% 1.19/1.44      ((~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 1.19/1.44         <= (~
% 1.19/1.44             ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('46', plain,
% 1.19/1.44      (~ ((r2_hidden @ sk_A @ sk_E)) | ~ ((r2_hidden @ sk_B @ sk_F)) | 
% 1.19/1.44       ~ ((r2_hidden @ sk_C @ sk_G)) | 
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['44', '45'])).
% 1.19/1.44  thf('47', plain, ((r2_hidden @ sk_D @ sk_H)),
% 1.19/1.44      inference('clc', [status(thm)], ['32', '37'])).
% 1.19/1.44  thf('48', plain,
% 1.19/1.44      ((~ (r2_hidden @ sk_D @ sk_H)) <= (~ ((r2_hidden @ sk_D @ sk_H)))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('49', plain, (((r2_hidden @ sk_D @ sk_H))),
% 1.19/1.44      inference('sup-', [status(thm)], ['47', '48'])).
% 1.19/1.44  thf('50', plain,
% 1.19/1.44      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 1.19/1.44         (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['3', '8'])).
% 1.19/1.44  thf('51', plain,
% 1.19/1.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.19/1.44         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 1.19/1.44           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.19/1.44  thf('52', plain,
% 1.19/1.44      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.19/1.44         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.19/1.44           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.19/1.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.19/1.44  thf('53', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X0 @ X1)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('54', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 1.19/1.44          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ X4))),
% 1.19/1.44      inference('sup-', [status(thm)], ['52', '53'])).
% 1.19/1.44  thf('55', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.44         (~ (r2_hidden @ (k3_mcart_1 @ X5 @ X4 @ X3) @ 
% 1.19/1.44             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.19/1.44          | (r2_hidden @ (k4_tarski @ X5 @ X4) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['51', '54'])).
% 1.19/1.44  thf('56', plain,
% 1.19/1.44      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F)))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['50', '55'])).
% 1.19/1.44  thf('57', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X2 @ X3)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('58', plain,
% 1.19/1.44      (((r2_hidden @ sk_B @ sk_F))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.44  thf('59', plain,
% 1.19/1.44      ((~ (r2_hidden @ sk_B @ sk_F)) <= (~ ((r2_hidden @ sk_B @ sk_F)))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('60', plain,
% 1.19/1.44      (((r2_hidden @ sk_B @ sk_F)) | 
% 1.19/1.44       ~
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['58', '59'])).
% 1.19/1.44  thf('61', plain,
% 1.19/1.44      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F)))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['50', '55'])).
% 1.19/1.44  thf('62', plain,
% 1.19/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.44         ((r2_hidden @ X0 @ X1)
% 1.19/1.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.19/1.44      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.19/1.44  thf('63', plain,
% 1.19/1.44      (((r2_hidden @ sk_A @ sk_E))
% 1.19/1.44         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 1.19/1.44      inference('sup-', [status(thm)], ['61', '62'])).
% 1.19/1.44  thf('64', plain,
% 1.19/1.44      ((~ (r2_hidden @ sk_A @ sk_E)) <= (~ ((r2_hidden @ sk_A @ sk_E)))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('65', plain,
% 1.19/1.44      (((r2_hidden @ sk_A @ sk_E)) | 
% 1.19/1.44       ~
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('sup-', [status(thm)], ['63', '64'])).
% 1.19/1.44  thf('66', plain,
% 1.19/1.44      (~
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) | 
% 1.19/1.44       ~ ((r2_hidden @ sk_A @ sk_E)) | ~ ((r2_hidden @ sk_D @ sk_H)) | 
% 1.19/1.44       ~ ((r2_hidden @ sk_B @ sk_F)) | ~ ((r2_hidden @ sk_C @ sk_G))),
% 1.19/1.44      inference('split', [status(esa)], ['16'])).
% 1.19/1.44  thf('67', plain,
% 1.19/1.44      (((r2_hidden @ sk_A @ sk_E)) | 
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('split', [status(esa)], ['2'])).
% 1.19/1.44  thf('68', plain,
% 1.19/1.44      (((r2_hidden @ sk_B @ sk_F)) | 
% 1.19/1.44       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.44         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 1.19/1.44      inference('split', [status(esa)], ['20'])).
% 1.19/1.44  thf('69', plain, ($false),
% 1.19/1.44      inference('sat_resolution*', [status(thm)],
% 1.19/1.44                ['1', '18', '46', '49', '60', '65', '66', '67', '68'])).
% 1.19/1.44  
% 1.19/1.44  % SZS output end Refutation
% 1.19/1.44  
% 1.19/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
