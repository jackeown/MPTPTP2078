%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BFQYk4A0lY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:18 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 800 expanded)
%              Number of leaves         :   22 ( 248 expanded)
%              Depth                    :   17
%              Number of atoms          : 1124 (11013 expanded)
%              Number of equality atoms :   26 ( 394 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ( ~ ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t73_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
    <=> ( ( r2_hidden @ A @ D )
        & ( r2_hidden @ B @ E )
        & ( r2_hidden @ C @ F ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X19 @ X21 @ X22 ) @ ( k3_zfmisc_1 @ X20 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X6 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_F )
   <= ~ ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E )
   <= ~ ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ X23 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X19 @ X21 @ X22 ) @ ( k3_zfmisc_1 @ X20 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ X1 @ X5 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X5 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_G )
   <= ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X0 @ X4 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_H )
   <= ~ ( r2_hidden @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sat_resolution*',[status(thm)],['25','30','39','48','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,(
    r2_hidden @ sk_A @ sk_E ),
    inference('sat_resolution*',[status(thm)],['25','30','39','48','49','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_E ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    r2_hidden @ sk_B @ sk_F ),
    inference('sat_resolution*',[status(thm)],['25','30','39','48','49','58'])).

thf('60',plain,(
    r2_hidden @ sk_B @ sk_F ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['64'])).

thf('67',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference('sat_resolution*',[status(thm)],['25','30','39','48','49','66'])).

thf('68',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ sk_G ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('73',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('74',plain,(
    r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
   <= ( r2_hidden @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference('sat_resolution*',[status(thm)],['25','30','39','48','49','77'])).

thf('79',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_H ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ ( k4_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('85',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['51','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BFQYk4A0lY
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 1082 iterations in 0.688s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.91/1.14  thf(sk_E_type, type, sk_E: $i).
% 0.91/1.14  thf(sk_H_type, type, sk_H: $i).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.91/1.14  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.91/1.14  thf(sk_G_type, type, sk_G: $i).
% 0.91/1.14  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.91/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.14  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.91/1.14  thf(sk_F_type, type, sk_F: $i).
% 0.91/1.14  thf(t84_mcart_1, conjecture,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.91/1.14     ( ( r2_hidden @
% 0.91/1.14         ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 0.91/1.14       ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 0.91/1.14         ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.91/1.14        ( ( r2_hidden @
% 0.91/1.14            ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 0.91/1.14          ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 0.91/1.14            ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t84_mcart_1])).
% 0.91/1.14  thf('0', plain,
% 0.91/1.14      ((~ (r2_hidden @ sk_D @ sk_H)
% 0.91/1.14        | ~ (r2_hidden @ sk_C @ sk_G)
% 0.91/1.14        | ~ (r2_hidden @ sk_B @ sk_F)
% 0.91/1.14        | ~ (r2_hidden @ sk_A @ sk_E)
% 0.91/1.14        | ~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14             (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      ((~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      (((r2_hidden @ sk_A @ sk_E)
% 0.91/1.14        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('split', [status(esa)], ['2'])).
% 0.91/1.14  thf(d3_zfmisc_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.91/1.14       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.91/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.91/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.91/1.14      inference('sup+', [status(thm)], ['4', '5'])).
% 0.91/1.14  thf(t53_mcart_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.91/1.14       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.91/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17) @ 
% 0.91/1.14              X18))),
% 0.91/1.14      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.91/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.91/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.91/1.14      inference('demod', [status(thm)], ['6', '9'])).
% 0.91/1.14  thf(d3_mcart_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.91/1.14           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.91/1.14           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.91/1.14      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf(t31_mcart_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.91/1.14       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.91/1.14           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13) @ X14))),
% 0.91/1.14      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.91/1.14           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.91/1.14           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.14  thf('17', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.91/1.14      inference('demod', [status(thm)], ['13', '16'])).
% 0.91/1.14  thf(t73_mcart_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.14     ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 0.91/1.14       ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & ( r2_hidden @ C @ F ) ) ))).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.14         ((r2_hidden @ X19 @ X20)
% 0.91/1.14          | ~ (r2_hidden @ (k3_mcart_1 @ X19 @ X21 @ X22) @ 
% 0.91/1.14               (k3_zfmisc_1 @ X20 @ X23 @ X24)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_mcart_1])).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14             (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.91/1.14          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ X6))),
% 0.91/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.14  thf('20', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.91/1.14             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.91/1.14          | (r2_hidden @ (k4_tarski @ X7 @ X6) @ (k2_zfmisc_1 @ X3 @ X2)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['10', '19'])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F)))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['3', '20'])).
% 0.91/1.14  thf(l54_zfmisc_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.91/1.14       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((r2_hidden @ X2 @ X3)
% 0.91/1.14          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (((r2_hidden @ sk_B @ sk_F))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      ((~ (r2_hidden @ sk_B @ sk_F)) <= (~ ((r2_hidden @ sk_B @ sk_F)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (((r2_hidden @ sk_B @ sk_F)) | 
% 0.91/1.14       ~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F)))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['3', '20'])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((r2_hidden @ X0 @ X1)
% 0.91/1.14          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('28', plain,
% 0.91/1.14      (((r2_hidden @ sk_A @ sk_E))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.14  thf('29', plain,
% 0.91/1.14      ((~ (r2_hidden @ sk_A @ sk_E)) <= (~ ((r2_hidden @ sk_A @ sk_E)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      (((r2_hidden @ sk_A @ sk_E)) | 
% 0.91/1.14       ~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('split', [status(esa)], ['2'])).
% 0.91/1.14  thf('32', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.91/1.14      inference('demod', [status(thm)], ['6', '9'])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.91/1.14           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.91/1.14      inference('demod', [status(thm)], ['13', '16'])).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.14         ((r2_hidden @ X21 @ X23)
% 0.91/1.14          | ~ (r2_hidden @ (k3_mcart_1 @ X19 @ X21 @ X22) @ 
% 0.91/1.14               (k3_zfmisc_1 @ X20 @ X23 @ X24)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_mcart_1])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14             (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.91/1.14          | (r2_hidden @ X1 @ X5))),
% 0.91/1.14      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('36', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.91/1.14             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.91/1.14          | (r2_hidden @ X5 @ X1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (((r2_hidden @ sk_C @ sk_G))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['31', '36'])).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      ((~ (r2_hidden @ sk_C @ sk_G)) <= (~ ((r2_hidden @ sk_C @ sk_G)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      (((r2_hidden @ sk_C @ sk_G)) | 
% 0.91/1.14       ~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('split', [status(esa)], ['2'])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.91/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('42', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.91/1.14           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((r2_hidden @ X2 @ X3)
% 0.91/1.14          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('44', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14             (k2_zfmisc_1 @ X5 @ X4))
% 0.91/1.14          | (r2_hidden @ X0 @ X4))),
% 0.91/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.14  thf('45', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.91/1.14             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.91/1.14          | (r2_hidden @ X4 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['41', '44'])).
% 0.91/1.14  thf('46', plain,
% 0.91/1.14      (((r2_hidden @ sk_D @ sk_H))
% 0.91/1.14         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14               (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['40', '45'])).
% 0.91/1.14  thf('47', plain,
% 0.91/1.14      ((~ (r2_hidden @ sk_D @ sk_H)) <= (~ ((r2_hidden @ sk_D @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      (((r2_hidden @ sk_D @ sk_H)) | 
% 0.91/1.14       ~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) | 
% 0.91/1.14       ~ ((r2_hidden @ sk_B @ sk_F)) | ~ ((r2_hidden @ sk_A @ sk_E)) | 
% 0.91/1.14       ~ ((r2_hidden @ sk_D @ sk_H)) | ~ ((r2_hidden @ sk_C @ sk_G))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('50', plain,
% 0.91/1.14      (~
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['25', '30', '39', '48', '49'])).
% 0.91/1.14  thf('51', plain,
% 0.91/1.14      (~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.91/1.14  thf('52', plain,
% 0.91/1.14      (((r2_hidden @ sk_A @ sk_E)) <= (((r2_hidden @ sk_A @ sk_E)))),
% 0.91/1.14      inference('split', [status(esa)], ['2'])).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      (((r2_hidden @ sk_A @ sk_E)) | 
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['2'])).
% 0.91/1.14  thf('54', plain, (((r2_hidden @ sk_A @ sk_E))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['25', '30', '39', '48', '49', '53'])).
% 0.91/1.14  thf('55', plain, ((r2_hidden @ sk_A @ sk_E)),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (((r2_hidden @ sk_B @ sk_F)
% 0.91/1.14        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (((r2_hidden @ sk_B @ sk_F)) <= (((r2_hidden @ sk_B @ sk_F)))),
% 0.91/1.14      inference('split', [status(esa)], ['56'])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      (((r2_hidden @ sk_B @ sk_F)) | 
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['56'])).
% 0.91/1.14  thf('59', plain, (((r2_hidden @ sk_B @ sk_F))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['25', '30', '39', '48', '49', '58'])).
% 0.91/1.14  thf('60', plain, ((r2_hidden @ sk_B @ sk_F)),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.14         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.91/1.14          | ~ (r2_hidden @ X2 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('62', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.14          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_F)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.14  thf('63', plain,
% 0.91/1.14      ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.91/1.14      inference('sup-', [status(thm)], ['55', '62'])).
% 0.91/1.14  thf('64', plain,
% 0.91/1.14      (((r2_hidden @ sk_C @ sk_G)
% 0.91/1.14        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('65', plain,
% 0.91/1.14      (((r2_hidden @ sk_C @ sk_G)) <= (((r2_hidden @ sk_C @ sk_G)))),
% 0.91/1.14      inference('split', [status(esa)], ['64'])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (((r2_hidden @ sk_C @ sk_G)) | 
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['64'])).
% 0.91/1.14  thf('67', plain, (((r2_hidden @ sk_C @ sk_G))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['25', '30', '39', '48', '49', '66'])).
% 0.91/1.14  thf('68', plain, ((r2_hidden @ sk_C @ sk_G)),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.14         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.91/1.14          | ~ (r2_hidden @ X2 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('70', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.14          | (r2_hidden @ (k4_tarski @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_G)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['68', '69'])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      ((r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 0.91/1.14        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ sk_G))),
% 0.91/1.14      inference('sup-', [status(thm)], ['63', '70'])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.91/1.14           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.14         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.91/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.91/1.14        (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.91/1.14      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.91/1.14  thf('75', plain,
% 0.91/1.14      (((r2_hidden @ sk_D @ sk_H)
% 0.91/1.14        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14           (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('76', plain,
% 0.91/1.14      (((r2_hidden @ sk_D @ sk_H)) <= (((r2_hidden @ sk_D @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['75'])).
% 0.91/1.14  thf('77', plain,
% 0.91/1.14      (((r2_hidden @ sk_D @ sk_H)) | 
% 0.91/1.14       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14         (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.91/1.14      inference('split', [status(esa)], ['75'])).
% 0.91/1.14  thf('78', plain, (((r2_hidden @ sk_D @ sk_H))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['25', '30', '39', '48', '49', '77'])).
% 0.91/1.14  thf('79', plain, ((r2_hidden @ sk_D @ sk_H)),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.14         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.91/1.14          | ~ (r2_hidden @ X2 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.14  thf('81', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.14          | (r2_hidden @ (k4_tarski @ X1 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_H)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['79', '80'])).
% 0.91/1.14  thf('82', plain,
% 0.91/1.14      ((r2_hidden @ (k4_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_D) @ 
% 0.91/1.14        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H))),
% 0.91/1.14      inference('sup-', [status(thm)], ['74', '81'])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.91/1.14           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 0.91/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.14  thf('84', plain,
% 0.91/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.91/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.91/1.14        (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.91/1.14      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.91/1.14  thf('86', plain, ($false), inference('demod', [status(thm)], ['51', '85'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
