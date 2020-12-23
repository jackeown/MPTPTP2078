%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aF9S4vduC1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:41 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  222 (256099 expanded)
%              Number of leaves         :   17 (69219 expanded)
%              Depth                    :   71
%              Number of atoms          : 2152 (3688680 expanded)
%              Number of equality atoms :  440 (688253 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t57_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
            = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_mcart_1])).

thf('0',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( D = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10 )
       != ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17 ) )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X2 = sk_B )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference(eq_res,[status(thm)],['4'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_F = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = sk_B ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D @ X0 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D @ X0 )
      = ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10 )
       != ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('53',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 ) )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['42','72'])).

thf('74',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('77',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['41','81'])).

thf('83',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('84',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_C ) @ sk_D @ X0 )
      = ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 ) ) ),
    inference(demod,[status(thm)],['40','84'])).

thf('86',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_C ) @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('91',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('93',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90','93'])).

thf('95',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference(condensation,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_F = sk_B ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_F = sk_B ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('110',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_F = sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('112',plain,(
    sk_F = sk_B ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('117',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('121',plain,(
    sk_F = sk_B ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('122',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('124',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('125',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10 )
       != ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17 ) )
      | ( X11 = X16 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(eq_res,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['123','129'])).

thf('131',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('132',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['122','134'])).

thf('136',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('137',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(condensation,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('154',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('156',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( sk_D != sk_H )
    | ( sk_C != sk_G )
    | ( sk_A != sk_E )
    | ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('161',plain,(
    sk_D != sk_H ),
    inference('sat_resolution*',[status(thm)],['115','119','159','160'])).

thf('162',plain,(
    sk_D != sk_H ),
    inference(simpl_trail,[status(thm)],['1','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('164',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('165',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('166',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('168',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('169',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10 )
       != ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17 ) )
      | ( X10 = X17 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_D = X0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(eq_res,[status(thm)],['170'])).

thf('172',plain,(
    sk_D != sk_H ),
    inference(simpl_trail,[status(thm)],['1','161'])).

thf('173',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','175'])).

thf('177',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('178',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_G )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0 ) )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['166','188'])).

thf('190',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('191',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['189','190'])).

thf('192',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['189','190'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != sk_E )
      | ( X0 = sk_E ) ) ),
    inference(demod,[status(thm)],['163','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('195',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['189','190'])).

thf('196',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['189','190'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ sk_E @ X1 @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ sk_E @ X1 @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( sk_E != sk_E )
      | ( X0 = sk_E ) ) ),
    inference(demod,[status(thm)],['193','197','198'])).

thf('200',plain,(
    ! [X0: $i] : ( X0 = sk_E ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i] : ( X0 = sk_E ) ),
    inference(simplify,[status(thm)],['199'])).

thf('202',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['162','200','201'])).

thf('203',plain,(
    $false ),
    inference(simplify,[status(thm)],['202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aF9S4vduC1
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.57/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.57/1.78  % Solved by: fo/fo7.sh
% 1.57/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.57/1.78  % done 1787 iterations in 1.311s
% 1.57/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.57/1.78  % SZS output start Refutation
% 1.57/1.78  thf(sk_F_type, type, sk_F: $i).
% 1.57/1.78  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.57/1.78  thf(sk_D_type, type, sk_D: $i).
% 1.57/1.78  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.57/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.57/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.57/1.78  thf(sk_G_type, type, sk_G: $i).
% 1.57/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.57/1.78  thf(sk_E_type, type, sk_E: $i).
% 1.57/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.57/1.78  thf(sk_H_type, type, sk_H: $i).
% 1.57/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.57/1.78  thf(t57_mcart_1, conjecture,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.57/1.78     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.57/1.78       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.57/1.78         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.57/1.78           ( ( D ) = ( H ) ) ) ) ))).
% 1.57/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.57/1.78    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.57/1.78        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.57/1.78          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.57/1.78            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.57/1.78              ( ( D ) = ( H ) ) ) ) ) )),
% 1.57/1.78    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 1.57/1.78  thf('0', plain,
% 1.57/1.78      ((((sk_A) != (sk_E))
% 1.57/1.78        | ((sk_B) != (sk_F))
% 1.57/1.78        | ((sk_C) != (sk_G))
% 1.57/1.78        | ((sk_D) != (sk_H)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('1', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.57/1.78      inference('split', [status(esa)], ['0'])).
% 1.57/1.78  thf('2', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(t56_mcart_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.57/1.78     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.57/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.57/1.78         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 1.57/1.78         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.57/1.78           ( ( D ) = ( H ) ) ) ) ))).
% 1.57/1.78  thf('3', plain,
% 1.57/1.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.57/1.78         X17 : $i]:
% 1.57/1.78         (((X10) = (k1_xboole_0))
% 1.57/1.78          | ((X11) = (k1_xboole_0))
% 1.57/1.78          | ((X12) = (k1_xboole_0))
% 1.57/1.78          | ((X13) = (k1_xboole_0))
% 1.57/1.78          | ((k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10)
% 1.57/1.78              != (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17))
% 1.57/1.78          | ((X12) = (X15)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t56_mcart_1])).
% 1.57/1.78  thf('4', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.57/1.78            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.57/1.78          | ((X2) = (sk_B))
% 1.57/1.78          | ((X3) = (k1_xboole_0))
% 1.57/1.78          | ((X2) = (k1_xboole_0))
% 1.57/1.78          | ((X1) = (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.57/1.78  thf('5', plain,
% 1.57/1.78      ((((sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('eq_res', [status(thm)], ['4'])).
% 1.57/1.78  thf(t113_zfmisc_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.57/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.57/1.78  thf('6', plain,
% 1.57/1.78      (![X1 : $i, X2 : $i]:
% 1.57/1.78         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.57/1.78  thf('7', plain,
% 1.57/1.78      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['6'])).
% 1.57/1.78  thf(d4_zfmisc_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.57/1.78     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.57/1.78       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.57/1.78  thf('8', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('9', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.57/1.78  thf('10', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_G) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['5', '9'])).
% 1.57/1.78  thf('11', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('12', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('13', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('14', plain,
% 1.57/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['10', '13'])).
% 1.57/1.78  thf('15', plain,
% 1.57/1.78      ((((sk_F) = (sk_B))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['14'])).
% 1.57/1.78  thf('16', plain,
% 1.57/1.78      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['6'])).
% 1.57/1.78  thf(d3_zfmisc_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.57/1.78       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.57/1.78  thf('17', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('18', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['16', '17'])).
% 1.57/1.78  thf('19', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('20', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 1.57/1.78           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['18', '19'])).
% 1.57/1.78  thf('21', plain,
% 1.57/1.78      (![X1 : $i, X2 : $i]:
% 1.57/1.78         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.57/1.78  thf('22', plain,
% 1.57/1.78      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['21'])).
% 1.57/1.78  thf('23', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['20', '22'])).
% 1.57/1.78  thf('24', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['15', '23'])).
% 1.57/1.78  thf('25', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('26', plain,
% 1.57/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (sk_B))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['24', '25'])).
% 1.57/1.78  thf('27', plain,
% 1.57/1.78      ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)) | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['26'])).
% 1.57/1.78  thf('28', plain,
% 1.57/1.78      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['6'])).
% 1.57/1.78  thf('29', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('30', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 1.57/1.78           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['28', '29'])).
% 1.57/1.78  thf('31', plain,
% 1.57/1.78      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['21'])).
% 1.57/1.78  thf('32', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['30', '31'])).
% 1.57/1.78  thf('33', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ X1 @ sk_F @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['27', '32'])).
% 1.57/1.78  thf('34', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('35', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('36', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('37', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 1.57/1.78           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.57/1.78      inference('sup+', [status(thm)], ['35', '36'])).
% 1.57/1.78  thf('38', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D @ X0)
% 1.57/1.78           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['34', '37'])).
% 1.57/1.78  thf('39', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 1.57/1.78           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.57/1.78      inference('sup+', [status(thm)], ['35', '36'])).
% 1.57/1.78  thf('40', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D @ X0)
% 1.57/1.78           = (k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['38', '39'])).
% 1.57/1.78  thf('41', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('42', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('43', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('44', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('45', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('46', plain,
% 1.57/1.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.57/1.78         X17 : $i]:
% 1.57/1.78         (((X10) = (k1_xboole_0))
% 1.57/1.78          | ((X11) = (k1_xboole_0))
% 1.57/1.78          | ((X12) = (k1_xboole_0))
% 1.57/1.78          | ((X13) = (k1_xboole_0))
% 1.57/1.78          | ((k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10)
% 1.57/1.78              != (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17))
% 1.57/1.78          | ((X13) = (X14)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t56_mcart_1])).
% 1.57/1.78  thf('47', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.57/1.78            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.57/1.78          | ((sk_A) = (X3))
% 1.57/1.78          | ((sk_A) = (k1_xboole_0))
% 1.57/1.78          | ((sk_B) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (k1_xboole_0))
% 1.57/1.78          | ((sk_D) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['45', '46'])).
% 1.57/1.78  thf('48', plain,
% 1.57/1.78      ((((sk_D) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_B) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('eq_res', [status(thm)], ['47'])).
% 1.57/1.78  thf('49', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.57/1.78  thf('50', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0))
% 1.57/1.78          | ((sk_A) = (sk_E))
% 1.57/1.78          | ((sk_A) = (k1_xboole_0))
% 1.57/1.78          | ((sk_B) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['48', '49'])).
% 1.57/1.78  thf('51', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_B) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['44', '50'])).
% 1.57/1.78  thf('52', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('53', plain,
% 1.57/1.78      ((((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_B) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 1.57/1.78  thf('54', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['20', '22'])).
% 1.57/1.78  thf('55', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_A) = (sk_E))
% 1.57/1.78          | ((sk_A) = (k1_xboole_0))
% 1.57/1.78          | ((sk_B) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['53', '54'])).
% 1.57/1.78  thf('56', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_B) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['43', '55'])).
% 1.57/1.78  thf('57', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('58', plain,
% 1.57/1.78      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 1.57/1.78  thf('59', plain,
% 1.57/1.78      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['6'])).
% 1.57/1.78  thf('60', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('61', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('62', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.57/1.78      inference('sup+', [status(thm)], ['60', '61'])).
% 1.57/1.78  thf('63', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('64', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.57/1.78           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.57/1.78      inference('demod', [status(thm)], ['62', '63'])).
% 1.57/1.78  thf('65', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.57/1.78           = (k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['59', '64'])).
% 1.57/1.78  thf('66', plain,
% 1.57/1.78      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['21'])).
% 1.57/1.78  thf('67', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('68', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.57/1.78           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['66', '67'])).
% 1.57/1.78  thf('69', plain,
% 1.57/1.78      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['21'])).
% 1.57/1.78  thf('70', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('71', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k1_xboole_0) = (k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['65', '70'])).
% 1.57/1.78  thf('72', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_xboole_0) = (k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0))
% 1.57/1.78          | ((sk_A) = (sk_E))
% 1.57/1.78          | ((sk_A) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['58', '71'])).
% 1.57/1.78  thf('73', plain,
% 1.57/1.78      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.57/1.78        | ((sk_A) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['42', '72'])).
% 1.57/1.78  thf('74', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('75', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 1.57/1.78  thf('76', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('77', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('78', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 1.57/1.78           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['76', '77'])).
% 1.57/1.78  thf('79', plain,
% 1.57/1.78      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['21'])).
% 1.57/1.78  thf('80', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['78', '79'])).
% 1.57/1.78  thf('81', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['75', '80'])).
% 1.57/1.78  thf('82', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_A) = (sk_E)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['41', '81'])).
% 1.57/1.78  thf('83', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('84', plain, (((sk_A) = (sk_E))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.57/1.78  thf('85', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_B @ sk_C) @ sk_D @ X0)
% 1.57/1.78           = (k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['40', '84'])).
% 1.57/1.78  thf('86', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 1.57/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.57/1.78  thf('87', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((X0) = (k1_xboole_0))
% 1.57/1.78          | ((X1) = (k1_xboole_0))
% 1.57/1.78          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.57/1.78  thf('88', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['86', '87'])).
% 1.57/1.78  thf('89', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0))
% 1.57/1.78          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_B @ sk_C) @ sk_D)
% 1.57/1.78              = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['85', '88'])).
% 1.57/1.78  thf('90', plain,
% 1.57/1.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 1.57/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.57/1.78  thf('91', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('92', plain, (((sk_A) = (sk_E))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.57/1.78  thf('93', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92'])).
% 1.57/1.78  thf('94', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0))
% 1.57/1.78          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['89', '90', '93'])).
% 1.57/1.78  thf('95', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('96', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('97', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['33', '96'])).
% 1.57/1.78  thf('98', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('99', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['97', '98'])).
% 1.57/1.78  thf('100', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((X0) = (k1_xboole_0)) | ((sk_F) = (sk_B)) | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['99'])).
% 1.57/1.78  thf('101', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('condensation', [status(thm)], ['100'])).
% 1.57/1.78  thf('102', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('103', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ sk_E @ X1 @ X0) = (k1_xboole_0)) | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['101', '102'])).
% 1.57/1.78  thf('104', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('105', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['103', '104'])).
% 1.57/1.78  thf('106', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('107', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (sk_B))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['105', '106'])).
% 1.57/1.78  thf('108', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['107'])).
% 1.57/1.78  thf('109', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92'])).
% 1.57/1.78  thf('110', plain,
% 1.57/1.78      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.57/1.78        | ((sk_F) = (sk_B)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['108', '109'])).
% 1.57/1.78  thf('111', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('112', plain, (((sk_F) = (sk_B))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 1.57/1.78  thf('113', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.57/1.78      inference('split', [status(esa)], ['0'])).
% 1.57/1.78  thf('114', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['112', '113'])).
% 1.57/1.78  thf('115', plain, ((((sk_B) = (sk_F)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['114'])).
% 1.57/1.78  thf('116', plain, (((sk_A) = (sk_E))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.57/1.78  thf('117', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.57/1.78      inference('split', [status(esa)], ['0'])).
% 1.57/1.78  thf('118', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['116', '117'])).
% 1.57/1.78  thf('119', plain, ((((sk_A) = (sk_E)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['118'])).
% 1.57/1.78  thf('120', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92'])).
% 1.57/1.78  thf('121', plain, (((sk_F) = (sk_B))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 1.57/1.78  thf('122', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.57/1.78  thf('123', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.57/1.78  thf('124', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.57/1.78  thf('125', plain,
% 1.57/1.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.57/1.78         X17 : $i]:
% 1.57/1.78         (((X10) = (k1_xboole_0))
% 1.57/1.78          | ((X11) = (k1_xboole_0))
% 1.57/1.78          | ((X12) = (k1_xboole_0))
% 1.57/1.78          | ((X13) = (k1_xboole_0))
% 1.57/1.78          | ((k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10)
% 1.57/1.78              != (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17))
% 1.57/1.78          | ((X11) = (X16)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t56_mcart_1])).
% 1.57/1.78  thf('126', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.57/1.78            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.57/1.78          | ((sk_C) = (X1))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (k1_xboole_0))
% 1.57/1.78          | ((sk_D) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['124', '125'])).
% 1.57/1.78  thf('127', plain,
% 1.57/1.78      ((((sk_D) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('eq_res', [status(thm)], ['126'])).
% 1.57/1.78  thf('128', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.57/1.78  thf('129', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['127', '128'])).
% 1.57/1.78  thf('130', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['123', '129'])).
% 1.57/1.78  thf('131', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('132', plain,
% 1.57/1.78      ((((sk_C) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 1.57/1.78  thf('133', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['20', '22'])).
% 1.57/1.78  thf('134', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['132', '133'])).
% 1.57/1.78  thf('135', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['122', '134'])).
% 1.57/1.78  thf('136', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('137', plain,
% 1.57/1.78      ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 1.57/1.78  thf('138', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['30', '31'])).
% 1.57/1.78  thf('139', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ X1 @ sk_F @ X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['137', '138'])).
% 1.57/1.78  thf('140', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('141', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['139', '140'])).
% 1.57/1.78  thf('142', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('143', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['141', '142'])).
% 1.57/1.78  thf('144', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((X0) = (k1_xboole_0)) | ((sk_C) = (sk_G)) | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['143'])).
% 1.57/1.78  thf('145', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('condensation', [status(thm)], ['144'])).
% 1.57/1.78  thf('146', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('147', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ sk_E @ X1 @ X0) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['145', '146'])).
% 1.57/1.78  thf('148', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('149', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['147', '148'])).
% 1.57/1.78  thf('150', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('151', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_C) = (sk_G))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['149', '150'])).
% 1.57/1.78  thf('152', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['151'])).
% 1.57/1.78  thf('153', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.57/1.78  thf('154', plain,
% 1.57/1.78      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.57/1.78        | ((sk_C) = (sk_G)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['152', '153'])).
% 1.57/1.78  thf('155', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('156', plain, (((sk_C) = (sk_G))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 1.57/1.78  thf('157', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.57/1.78      inference('split', [status(esa)], ['0'])).
% 1.57/1.78  thf('158', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['156', '157'])).
% 1.57/1.78  thf('159', plain, ((((sk_C) = (sk_G)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['158'])).
% 1.57/1.78  thf('160', plain,
% 1.57/1.78      (~ (((sk_D) = (sk_H))) | ~ (((sk_C) = (sk_G))) | ~ (((sk_A) = (sk_E))) | 
% 1.57/1.78       ~ (((sk_B) = (sk_F)))),
% 1.57/1.78      inference('split', [status(esa)], ['0'])).
% 1.57/1.78  thf('161', plain, (~ (((sk_D) = (sk_H)))),
% 1.57/1.78      inference('sat_resolution*', [status(thm)], ['115', '119', '159', '160'])).
% 1.57/1.78  thf('162', plain, (((sk_D) != (sk_H))),
% 1.57/1.78      inference('simpl_trail', [status(thm)], ['1', '161'])).
% 1.57/1.78  thf('163', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('164', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.57/1.78  thf('165', plain, (((sk_C) = (sk_G))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 1.57/1.78  thf('166', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['164', '165'])).
% 1.57/1.78  thf('167', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['164', '165'])).
% 1.57/1.78  thf('168', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D)
% 1.57/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.57/1.78      inference('demod', [status(thm)], ['164', '165'])).
% 1.57/1.78  thf('169', plain,
% 1.57/1.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.57/1.78         X17 : $i]:
% 1.57/1.78         (((X10) = (k1_xboole_0))
% 1.57/1.78          | ((X11) = (k1_xboole_0))
% 1.57/1.78          | ((X12) = (k1_xboole_0))
% 1.57/1.78          | ((X13) = (k1_xboole_0))
% 1.57/1.78          | ((k4_zfmisc_1 @ X13 @ X12 @ X11 @ X10)
% 1.57/1.78              != (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X17))
% 1.57/1.78          | ((X10) = (X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t56_mcart_1])).
% 1.57/1.78  thf('170', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.57/1.78            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.57/1.78          | ((sk_D) = (X0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_G) = (k1_xboole_0))
% 1.57/1.78          | ((sk_D) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['168', '169'])).
% 1.57/1.78  thf('171', plain,
% 1.57/1.78      ((((sk_D) = (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0))
% 1.57/1.78        | ((sk_D) = (sk_H)))),
% 1.57/1.78      inference('eq_res', [status(thm)], ['170'])).
% 1.57/1.78  thf('172', plain, (((sk_D) != (sk_H))),
% 1.57/1.78      inference('simpl_trail', [status(thm)], ['1', '161'])).
% 1.57/1.78  thf('173', plain,
% 1.57/1.78      ((((sk_D) = (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['171', '172'])).
% 1.57/1.78  thf('174', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.57/1.78  thf('175', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_G) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['173', '174'])).
% 1.57/1.78  thf('176', plain,
% 1.57/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.57/1.78        | ((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['167', '175'])).
% 1.57/1.78  thf('177', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('178', plain,
% 1.57/1.78      ((((sk_G) = (k1_xboole_0))
% 1.57/1.78        | ((sk_F) = (k1_xboole_0))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 1.57/1.78  thf('179', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['16', '17'])).
% 1.57/1.78  thf('180', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ X1 @ X0 @ sk_G) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['178', '179'])).
% 1.57/1.78  thf('181', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('182', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['180', '181'])).
% 1.57/1.78  thf('183', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('184', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((X0) = (k1_xboole_0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['182', '183'])).
% 1.57/1.78  thf('185', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((X0) = (k1_xboole_0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0))
% 1.57/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['184'])).
% 1.57/1.78  thf('186', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('condensation', [status(thm)], ['185'])).
% 1.57/1.78  thf('187', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k1_xboole_0) = (k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['65', '70'])).
% 1.57/1.78  thf('188', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_xboole_0) = (k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0))
% 1.57/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['186', '187'])).
% 1.57/1.78  thf('189', plain,
% 1.57/1.78      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.57/1.78        | ((sk_E) = (k1_xboole_0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['166', '188'])).
% 1.57/1.78  thf('190', plain,
% 1.57/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('191', plain, (((sk_E) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['189', '190'])).
% 1.57/1.78  thf('192', plain, (((sk_E) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['189', '190'])).
% 1.57/1.78  thf('193', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.57/1.78            != (sk_E))
% 1.57/1.78          | ((X0) = (sk_E)))),
% 1.57/1.78      inference('demod', [status(thm)], ['163', '191', '192'])).
% 1.57/1.78  thf('194', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('195', plain, (((sk_E) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['189', '190'])).
% 1.57/1.78  thf('196', plain, (((sk_E) = (k1_xboole_0))),
% 1.57/1.78      inference('simplify_reflect-', [status(thm)], ['189', '190'])).
% 1.57/1.78  thf('197', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_E @ X1 @ X0) = (sk_E))),
% 1.57/1.78      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.57/1.78  thf('198', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_E @ X1 @ X0) = (sk_E))),
% 1.57/1.78      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.57/1.78  thf('199', plain, (![X0 : $i]: (((sk_E) != (sk_E)) | ((X0) = (sk_E)))),
% 1.57/1.78      inference('demod', [status(thm)], ['193', '197', '198'])).
% 1.57/1.78  thf('200', plain, (![X0 : $i]: ((X0) = (sk_E))),
% 1.57/1.78      inference('simplify', [status(thm)], ['199'])).
% 1.57/1.78  thf('201', plain, (![X0 : $i]: ((X0) = (sk_E))),
% 1.57/1.78      inference('simplify', [status(thm)], ['199'])).
% 1.57/1.78  thf('202', plain, (((sk_E) != (sk_E))),
% 1.57/1.78      inference('demod', [status(thm)], ['162', '200', '201'])).
% 1.57/1.78  thf('203', plain, ($false), inference('simplify', [status(thm)], ['202'])).
% 1.57/1.78  
% 1.57/1.78  % SZS output end Refutation
% 1.57/1.78  
% 1.57/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
