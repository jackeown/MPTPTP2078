%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0924+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iRENZ33cGc

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:43 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 509 expanded)
%              Number of leaves         :   21 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  931 (7291 expanded)
%              Number of equality atoms :   15 ( 180 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 @ X15 )
      = ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t73_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
    <=> ( ( r2_hidden @ A @ D )
        & ( r2_hidden @ B @ E )
        & ( r2_hidden @ C @ F ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X16 @ X18 @ X19 ) @ ( k3_zfmisc_1 @ X17 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ X1 @ X5 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X5 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference(clc,[status(thm)],['2','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_G )
   <= ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 @ X15 )
      = ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ X21 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X16 @ X18 @ X19 ) @ ( k3_zfmisc_1 @ X17 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ X0 @ X4 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_H )
   <= ~ ( r2_hidden @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 @ X15 )
      = ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X16 @ X18 @ X19 ) @ ( k3_zfmisc_1 @ X17 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X6 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_F )
   <= ~ ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E )
   <= ~ ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ~ ( r2_hidden @ sk_B @ sk_F )
    | ~ ( r2_hidden @ sk_A @ sk_E )
    | ~ ( r2_hidden @ sk_D @ sk_H )
    | ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sat_resolution*',[status(thm)],['14','24','35','40','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference(clc,[status(thm)],['2','11'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
   <= ( r2_hidden @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
   <= ( r2_hidden @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) )
   <= ( r2_hidden @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_E )
      & ( r2_hidden @ sk_B @ sk_F ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_E )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['15'])).

thf('52',plain,(
    r2_hidden @ sk_A @ sk_E ),
    inference('sat_resolution*',[status(thm)],['14','24','35','40','41','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ sk_F )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,(
    r2_hidden @ sk_B @ sk_F ),
    inference('sat_resolution*',[status(thm)],['14','24','35','40','41','53'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['50','52','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
   <= ( r2_hidden @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_D @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference('sat_resolution*',[status(thm)],['14','24','35','40','41','58'])).

thf('60',plain,(
    r2_hidden @ sk_D @ sk_H ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ X16 @ X18 @ X19 ) @ ( k3_zfmisc_1 @ X17 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X19 @ X22 )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k3_mcart_1 @ X1 @ X3 @ sk_D ) @ ( k3_zfmisc_1 @ X0 @ X2 @ sk_H ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) @ X1 @ sk_D ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 @ sk_H ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 @ X15 )
      = ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ X1 @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ sk_H ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['44','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['43','67'])).


%------------------------------------------------------------------------------
