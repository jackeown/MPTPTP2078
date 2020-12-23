%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCmLgY0nHJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:18 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 516 expanded)
%              Number of leaves         :   35 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          : 1105 (6100 expanded)
%              Number of equality atoms :  128 ( 875 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t33_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_mcart_1 @ A @ B @ C @ D )
          = ( k4_mcart_1 @ E @ F @ G @ H ) )
       => ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_mcart_1])).

thf('0',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C_1 != sk_G )
    | ( sk_D_1 != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_D_1 != sk_H )
   <= ( sk_D_1 != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_mcart_1 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X47 @ X48 ) @ X49 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_mcart_1 @ X38 ) )
      | ( X41 = X42 )
      | ( X38
       != ( k4_tarski @ X42 @ X43 ) )
      | ( X38
       != ( k4_tarski @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('6',plain,(
    ! [X39: $i,X40: $i,X42: $i,X43: $i] :
      ( ( ( k4_tarski @ X42 @ X43 )
       != ( k4_tarski @ X39 @ X40 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X42 @ X43 ) )
        = X42 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) )
    = ( k4_tarski @ ( k4_tarski @ sk_E @ sk_F ) @ sk_G ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('11',plain,
    ( ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k4_tarski @ ( k4_tarski @ sk_E @ sk_F ) @ sk_G ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('13',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('15',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('17',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('19',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('21',plain,
    ( ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k4_tarski @ ( k4_tarski @ sk_E @ sk_F ) @ sk_G ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ ( k4_tarski @ sk_E @ sk_F ) @ sk_G @ X0 @ X1 ) )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_mcart_1 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X47 @ X48 ) @ X49 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('25',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_mcart_1 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X47 @ X48 ) @ X49 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k4_tarski @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_mcart_1 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X47 @ X48 ) @ X49 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ X0 )
      = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','27','28'])).

thf('30',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ X0 )
      = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_H ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_mcart_1 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X47 @ X48 ) @ X49 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( r1_xboole_0 @ ( k2_tarski @ X32 @ X34 ) @ X33 )
      | ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t88_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X23 @ X23 @ X23 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t86_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k6_enumset1 @ X18 @ X18 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) )
      | ( X30 != X31 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('52',plain,(
    ! [X31: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X29 ) ) )
      | ( X27 != X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X29 ) @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('60',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_mcart_1 @ X44 )
        = X46 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ ( k1_tarski @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','61'])).

thf('63',plain,
    ( ( k2_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) )
    = sk_H ),
    inference('sup+',[status(thm)],['32','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','61'])).

thf('65',plain,(
    sk_D_1 = sk_H ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_D_1 != sk_H ) ),
    inference(demod,[status(thm)],['1','65'])).

thf('67',plain,
    ( $false
   <= ( sk_D_1 != sk_H ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('69',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('71',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X5 @ ( k1_tarski @ X4 ) ) )
      | ( X1 = X4 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( sk_G = X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( sk_G = X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_G = sk_C_1 ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( sk_C_1 != sk_G )
   <= ( sk_C_1 != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( sk_C_1 != sk_G ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_C_1 = sk_G ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['17','18'])).

thf('81',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('85',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('86',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['17','18'])).

thf('87',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_A @ sk_F ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( sk_F = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_F = sk_B ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_D_1 != sk_H )
    | ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C_1 != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,(
    sk_D_1 != sk_H ),
    inference('sat_resolution*',[status(thm)],['79','83','93','94'])).

thf('96',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['67','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCmLgY0nHJ
% 0.13/0.38  % Computer   : n015.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 10:30:23 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.67/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.87  % Solved by: fo/fo7.sh
% 0.67/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.87  % done 690 iterations in 0.378s
% 0.67/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.87  % SZS output start Refutation
% 0.67/0.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.87  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.67/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.87  thf(sk_G_type, type, sk_G: $i).
% 0.67/0.87  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.67/0.87  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.67/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.67/0.87                                           $i > $i).
% 0.67/0.87  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.67/0.87  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.67/0.87  thf(sk_H_type, type, sk_H: $i).
% 0.67/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.87  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.67/0.87  thf(sk_F_type, type, sk_F: $i).
% 0.67/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.87  thf(sk_E_type, type, sk_E: $i).
% 0.67/0.87  thf(t33_mcart_1, conjecture,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.67/0.87     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.67/0.87       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.67/0.87         ( ( D ) = ( H ) ) ) ))).
% 0.67/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.87    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.67/0.87        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.67/0.87          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.67/0.87            ( ( D ) = ( H ) ) ) ) )),
% 0.67/0.87    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.67/0.87  thf('0', plain,
% 0.67/0.87      ((((sk_A) != (sk_E))
% 0.67/0.87        | ((sk_B) != (sk_F))
% 0.67/0.87        | ((sk_C_1) != (sk_G))
% 0.67/0.87        | ((sk_D_1) != (sk_H)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('1', plain, ((((sk_D_1) != (sk_H))) <= (~ (((sk_D_1) = (sk_H))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('2', plain,
% 0.67/0.87      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.67/0.87         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('3', plain,
% 0.67/0.87      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.67/0.87         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t31_mcart_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.67/0.87       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ X47 @ X48 @ X49 @ X50)
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X47 @ X48) @ X49) @ X50))),
% 0.67/0.87      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.67/0.87  thf(d1_mcart_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.67/0.87       ( ![B:$i]:
% 0.67/0.87         ( ( ( B ) = ( k1_mcart_1 @ A ) ) <=>
% 0.67/0.87           ( ![C:$i,D:$i]:
% 0.67/0.87             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( C ) ) ) ) ) ) ))).
% 0.67/0.87  thf('5', plain,
% 0.67/0.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.67/0.87         (((X41) != (k1_mcart_1 @ X38))
% 0.67/0.87          | ((X41) = (X42))
% 0.67/0.87          | ((X38) != (k4_tarski @ X42 @ X43))
% 0.67/0.87          | ((X38) != (k4_tarski @ X39 @ X40)))),
% 0.67/0.87      inference('cnf', [status(esa)], [d1_mcart_1])).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      (![X39 : $i, X40 : $i, X42 : $i, X43 : $i]:
% 0.67/0.87         (((k4_tarski @ X42 @ X43) != (k4_tarski @ X39 @ X40))
% 0.67/0.87          | ((k1_mcart_1 @ (k4_tarski @ X42 @ X43)) = (X42)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['5'])).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (((k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))
% 0.67/0.87         = (k4_tarski @ (k4_tarski @ sk_E @ sk_F) @ sk_G))),
% 0.67/0.87      inference('sup+', [status(thm)], ['3', '8'])).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.87  thf('11', plain,
% 0.67/0.87      (((k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.67/0.87         = (k4_tarski @ (k4_tarski @ sk_E @ sk_F) @ sk_G))),
% 0.67/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.87  thf('12', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('13', plain,
% 0.67/0.87      (((k1_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.67/0.87         = (k4_tarski @ sk_E @ sk_F))),
% 0.67/0.87      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('15', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.67/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.67/0.87  thf('16', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('17', plain, (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.67/0.87      inference('sup+', [status(thm)], ['15', '16'])).
% 0.67/0.87  thf('18', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('19', plain, (((sk_A) = (sk_E))),
% 0.67/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('20', plain,
% 0.67/0.87      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.67/0.87         = (k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H))),
% 0.67/0.87      inference('demod', [status(thm)], ['2', '19'])).
% 0.67/0.87  thf('21', plain,
% 0.67/0.87      (((k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.67/0.87         = (k4_tarski @ (k4_tarski @ sk_E @ sk_F) @ sk_G))),
% 0.67/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.87  thf('23', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ 
% 0.67/0.87           (k4_mcart_1 @ (k4_tarski @ sk_E @ sk_F) @ sk_G @ X0 @ X1))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1) @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['21', '22'])).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ X47 @ X48 @ X49 @ X50)
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X47 @ X48) @ X49) @ X50))),
% 0.67/0.87      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.67/0.87  thf('25', plain,
% 0.67/0.87      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ X47 @ X48 @ X49 @ X50)
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X47 @ X48) @ X49) @ X50))),
% 0.67/0.87      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.67/0.87  thf('26', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.67/0.87           = (k4_tarski @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.67/0.87      inference('sup+', [status(thm)], ['24', '25'])).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.67/0.87      inference('eq_res', [status(thm)], ['6'])).
% 0.67/0.87  thf('28', plain,
% 0.67/0.87      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ X47 @ X48 @ X49 @ X50)
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X47 @ X48) @ X49) @ X50))),
% 0.67/0.87      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.67/0.87  thf('29', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ sk_E @ sk_F @ sk_G @ X0)
% 0.67/0.87           = (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ X0))),
% 0.67/0.87      inference('demod', [status(thm)], ['23', '26', '27', '28'])).
% 0.67/0.87  thf('30', plain, (((sk_A) = (sk_E))),
% 0.67/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('31', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ sk_A @ sk_F @ sk_G @ X0)
% 0.67/0.87           = (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ X0))),
% 0.67/0.87      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.87  thf('32', plain,
% 0.67/0.87      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.67/0.87         = (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_H))),
% 0.67/0.87      inference('demod', [status(thm)], ['20', '31'])).
% 0.67/0.87  thf('33', plain,
% 0.67/0.87      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.67/0.87         ((k4_mcart_1 @ X47 @ X48 @ X49 @ X50)
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X47 @ X48) @ X49) @ X50))),
% 0.67/0.87      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.67/0.87  thf(t57_zfmisc_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.67/0.87          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.67/0.87  thf('34', plain,
% 0.67/0.87      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.67/0.87         ((r2_hidden @ X32 @ X33)
% 0.67/0.87          | (r1_xboole_0 @ (k2_tarski @ X32 @ X34) @ X33)
% 0.67/0.87          | (r2_hidden @ X34 @ X33))),
% 0.67/0.87      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.67/0.87  thf(t76_enumset1, axiom,
% 0.67/0.87    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.87  thf('35', plain,
% 0.67/0.87      (![X14 : $i]: ((k1_enumset1 @ X14 @ X14 @ X14) = (k1_tarski @ X14))),
% 0.67/0.87      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.67/0.87  thf(t78_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.67/0.87  thf('36', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.87         ((k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17)
% 0.67/0.87           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.67/0.87      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.67/0.87  thf(t55_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.87     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.67/0.87       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.67/0.87  thf('37', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.87         ((k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5)
% 0.67/0.87           = (k2_xboole_0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4) @ 
% 0.67/0.87              (k1_tarski @ X5)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.67/0.87  thf('38', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.67/0.87           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.87  thf(t88_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.67/0.87  thf('39', plain,
% 0.67/0.87      (![X23 : $i, X24 : $i]:
% 0.67/0.87         ((k4_enumset1 @ X23 @ X23 @ X23 @ X23 @ X23 @ X24)
% 0.67/0.87           = (k2_tarski @ X23 @ X24))),
% 0.67/0.87      inference('cnf', [status(esa)], [t88_enumset1])).
% 0.67/0.87  thf('40', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0))
% 0.67/0.87           = (k2_tarski @ X1 @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['38', '39'])).
% 0.67/0.87  thf('41', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ 
% 0.67/0.87           (k1_enumset1 @ X0 @ X0 @ X0)) = (k2_tarski @ X1 @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['35', '40'])).
% 0.67/0.87  thf('42', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.87         ((k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17)
% 0.67/0.87           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.67/0.87      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.67/0.87  thf(t66_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.67/0.87     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.67/0.87       ( k2_xboole_0 @
% 0.67/0.87         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.67/0.87  thf('43', plain,
% 0.67/0.87      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.67/0.87         X13 : $i]:
% 0.67/0.87         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.67/0.87           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 0.67/0.87              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.67/0.87  thf('44', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.87         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.67/0.87           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.67/0.87              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['42', '43'])).
% 0.67/0.87  thf(t86_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.67/0.87     ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E ) =
% 0.67/0.87       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.67/0.87  thf('45', plain,
% 0.67/0.87      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.87         ((k6_enumset1 @ X18 @ X18 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.67/0.87           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.67/0.87      inference('cnf', [status(esa)], [t86_enumset1])).
% 0.67/0.87  thf('46', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X4 @ X3) @ 
% 0.67/0.87           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['44', '45'])).
% 0.67/0.87  thf('47', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.67/0.87      inference('demod', [status(thm)], ['41', '46'])).
% 0.67/0.87  thf('48', plain,
% 0.67/0.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.87         ((k3_enumset1 @ X15 @ X15 @ X15 @ X16 @ X17)
% 0.67/0.87           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.67/0.87      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.67/0.87  thf('49', plain,
% 0.67/0.87      (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_enumset1 @ X0 @ X0 @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['47', '48'])).
% 0.67/0.87  thf('50', plain,
% 0.67/0.87      (![X14 : $i]: ((k1_enumset1 @ X14 @ X14 @ X14) = (k1_tarski @ X14))),
% 0.67/0.87      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.67/0.87  thf(t16_zfmisc_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.67/0.87          ( ( A ) = ( B ) ) ) ))).
% 0.67/0.87  thf('51', plain,
% 0.67/0.87      (![X30 : $i, X31 : $i]:
% 0.67/0.87         (~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31))
% 0.67/0.87          | ((X30) != (X31)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.67/0.87  thf('52', plain,
% 0.67/0.87      (![X31 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))),
% 0.67/0.87      inference('simplify', [status(thm)], ['51'])).
% 0.67/0.87  thf('53', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ~ (r1_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['50', '52'])).
% 0.67/0.87  thf('54', plain,
% 0.67/0.87      (![X0 : $i]: ~ (r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['49', '53'])).
% 0.67/0.87  thf('55', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['34', '54'])).
% 0.67/0.87  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['55'])).
% 0.67/0.87  thf(t129_zfmisc_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( r2_hidden @
% 0.67/0.87         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.67/0.87       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.67/0.87  thf('57', plain,
% 0.67/0.87      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.67/0.87         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ 
% 0.67/0.87           (k2_zfmisc_1 @ X26 @ (k1_tarski @ X29)))
% 0.67/0.87          | ((X27) != (X29))
% 0.67/0.87          | ~ (r2_hidden @ X25 @ X26))),
% 0.67/0.87      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.67/0.87  thf('58', plain,
% 0.67/0.87      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X25 @ X26)
% 0.67/0.87          | (r2_hidden @ (k4_tarski @ X25 @ X29) @ 
% 0.67/0.87             (k2_zfmisc_1 @ X26 @ (k1_tarski @ X29))))),
% 0.67/0.87      inference('simplify', [status(thm)], ['57'])).
% 0.67/0.87  thf('59', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.67/0.87          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['56', '58'])).
% 0.67/0.87  thf(t13_mcart_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.67/0.87       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.67/0.87         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.67/0.87  thf('60', plain,
% 0.67/0.87      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.67/0.87         (((k2_mcart_1 @ X44) = (X46))
% 0.67/0.87          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ (k1_tarski @ X46))))),
% 0.67/0.87      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.67/0.87  thf('61', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['59', '60'])).
% 0.67/0.87  thf('62', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['33', '61'])).
% 0.67/0.87  thf('63', plain,
% 0.67/0.87      (((k2_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)) = (sk_H))),
% 0.67/0.87      inference('sup+', [status(thm)], ['32', '62'])).
% 0.67/0.87  thf('64', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['33', '61'])).
% 0.67/0.87  thf('65', plain, (((sk_D_1) = (sk_H))),
% 0.67/0.87      inference('demod', [status(thm)], ['63', '64'])).
% 0.67/0.87  thf('66', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_D_1) = (sk_H))))),
% 0.67/0.87      inference('demod', [status(thm)], ['1', '65'])).
% 0.67/0.87  thf('67', plain, (($false) <= (~ (((sk_D_1) = (sk_H))))),
% 0.67/0.87      inference('simplify', [status(thm)], ['66'])).
% 0.67/0.87  thf('68', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.67/0.87          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['56', '58'])).
% 0.67/0.87  thf('69', plain,
% 0.67/0.87      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.67/0.87         = (k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H))),
% 0.67/0.87      inference('demod', [status(thm)], ['2', '19'])).
% 0.67/0.87  thf('70', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.87  thf('71', plain,
% 0.67/0.87      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.87         (((X27) = (X28))
% 0.67/0.87          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ 
% 0.67/0.87               (k2_zfmisc_1 @ X26 @ (k1_tarski @ X28))))),
% 0.67/0.87      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.67/0.87  thf('72', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.87         (~ (r2_hidden @ (k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) @ 
% 0.67/0.87             (k2_zfmisc_1 @ X5 @ (k1_tarski @ X4)))
% 0.67/0.87          | ((X1) = (X4)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.87  thf('73', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ 
% 0.67/0.87             (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)) @ 
% 0.67/0.87             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0)))
% 0.67/0.87          | ((sk_G) = (X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['69', '72'])).
% 0.67/0.87  thf('74', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.67/0.87           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.87  thf('75', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.67/0.87             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0)))
% 0.67/0.87          | ((sk_G) = (X0)))),
% 0.67/0.87      inference('demod', [status(thm)], ['73', '74'])).
% 0.67/0.87  thf('76', plain, (((sk_G) = (sk_C_1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['68', '75'])).
% 0.67/0.87  thf('77', plain, ((((sk_C_1) != (sk_G))) <= (~ (((sk_C_1) = (sk_G))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('78', plain, ((((sk_C_1) != (sk_C_1))) <= (~ (((sk_C_1) = (sk_G))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['76', '77'])).
% 0.67/0.87  thf('79', plain, ((((sk_C_1) = (sk_G)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['78'])).
% 0.67/0.87  thf('80', plain, (((sk_A) = (sk_E))),
% 0.67/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('81', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('82', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['80', '81'])).
% 0.67/0.87  thf('83', plain, ((((sk_A) = (sk_E)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['82'])).
% 0.67/0.87  thf('84', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.67/0.87          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['56', '58'])).
% 0.67/0.87  thf('85', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.67/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.67/0.87  thf('86', plain, (((sk_A) = (sk_E))),
% 0.67/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('87', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_A @ sk_F))),
% 0.67/0.87      inference('demod', [status(thm)], ['85', '86'])).
% 0.67/0.87  thf('88', plain,
% 0.67/0.87      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.87         (((X27) = (X28))
% 0.67/0.87          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ 
% 0.67/0.87               (k2_zfmisc_1 @ X26 @ (k1_tarski @ X28))))),
% 0.67/0.87      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.67/0.87  thf('89', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.67/0.87             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0)))
% 0.67/0.87          | ((sk_F) = (X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['87', '88'])).
% 0.67/0.87  thf('90', plain, (((sk_F) = (sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['84', '89'])).
% 0.67/0.87  thf('91', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('92', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['90', '91'])).
% 0.67/0.87  thf('93', plain, ((((sk_B) = (sk_F)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['92'])).
% 0.67/0.87  thf('94', plain,
% 0.67/0.87      (~ (((sk_D_1) = (sk_H))) | ~ (((sk_B) = (sk_F))) | 
% 0.67/0.87       ~ (((sk_A) = (sk_E))) | ~ (((sk_C_1) = (sk_G)))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('95', plain, (~ (((sk_D_1) = (sk_H)))),
% 0.67/0.87      inference('sat_resolution*', [status(thm)], ['79', '83', '93', '94'])).
% 0.67/0.87  thf('96', plain, ($false),
% 0.67/0.87      inference('simpl_trail', [status(thm)], ['67', '95'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
