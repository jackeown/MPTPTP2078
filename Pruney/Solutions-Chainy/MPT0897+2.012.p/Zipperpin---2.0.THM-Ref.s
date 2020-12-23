%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raUzURkrHJ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:41 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  174 (11395 expanded)
%              Number of leaves         :   20 (2946 expanded)
%              Depth                    :   40
%              Number of atoms          : 1671 (177905 expanded)
%              Number of equality atoms :  353 (34890 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
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

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13 )
       != ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference(eq_res,[status(thm)],['10'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['6','27'])).

thf('29',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('32',plain,(
    ! [X9: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['5','37'])).

thf('39',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( X9 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('42',plain,(
    ! [X10: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X10 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['4','47'])).

thf('49',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('50',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','50'])).

thf('52',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','50'])).

thf('53',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13 )
       != ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X2 = sk_B )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference(eq_res,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_F = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = sk_B ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_F = sk_B )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_F = sk_B )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_F = sk_B ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_F = sk_B ) ),
    inference('sup+',[status(thm)],['52','73'])).

thf('75',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('76',plain,(
    sk_F = sk_B ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','76'])).

thf('78',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','76'])).

thf('79',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','76'])).

thf('80',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13 )
       != ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X14 = X19 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X1 = sk_C )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference(eq_res,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_G = sk_C )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_G = sk_C )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_G = sk_C ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = sk_C )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_G = sk_C )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup+',[status(thm)],['79','95'])).

thf('97',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('98',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_G = sk_C ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup+',[status(thm)],['78','100'])).

thf('102',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('103',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['77','103'])).

thf('105',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['77','103'])).

thf('106',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','76'])).

thf('107',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = sk_D )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('112',plain,
    ( ( sk_D = sk_H )
    | ( sk_D = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('114',plain,
    ( ( sk_D = sk_H )
    | ( sk_D = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,(
    sk_F = sk_B ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('119',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['116'])).

thf('120',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('123',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['116'])).

thf('124',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('127',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['116'])).

thf('128',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( sk_D != sk_H )
    | ( sk_C != sk_G )
    | ( sk_A != sk_E )
    | ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['116'])).

thf('131',plain,(
    sk_D != sk_H ),
    inference('sat_resolution*',[status(thm)],['121','125','129','130'])).

thf('132',plain,(
    sk_D != sk_H ),
    inference(simpl_trail,[status(thm)],['117','131'])).

thf('133',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['115','132'])).

thf('134',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','137'])).

thf('139',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('140',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','142'])).

thf('144',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('145',plain,(
    sk_H = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('146',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != sk_H ),
    inference(demod,[status(thm)],['2','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('148',plain,(
    sk_H = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('149',plain,(
    sk_H = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
      = sk_H ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    sk_H != sk_H ),
    inference(demod,[status(thm)],['146','150'])).

thf('152',plain,(
    $false ),
    inference(simplify,[status(thm)],['151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raUzURkrHJ
% 0.14/0.38  % Computer   : n004.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 10:21:24 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 1294 iterations in 0.387s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(sk_G_type, type, sk_G: $i).
% 0.68/0.88  thf(sk_E_type, type, sk_E: $i).
% 0.68/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.88  thf(sk_H_type, type, sk_H: $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.68/0.88  thf(sk_F_type, type, sk_F: $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.88  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.68/0.88  thf(t57_mcart_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.68/0.88     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.68/0.88       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.68/0.88           ( ( D ) = ( H ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.68/0.88        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.68/0.88          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.68/0.88              ( ( D ) = ( H ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t56_mcart_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.68/0.88     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.68/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.68/0.88           ( ( D ) = ( H ) ) ) ) ))).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.68/0.88         X20 : $i]:
% 0.68/0.88         (((X13) = (k1_xboole_0))
% 0.68/0.88          | ((X14) = (k1_xboole_0))
% 0.68/0.88          | ((X15) = (k1_xboole_0))
% 0.68/0.88          | ((X16) = (k1_xboole_0))
% 0.68/0.88          | ((k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13)
% 0.68/0.88              != (k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20))
% 0.68/0.88          | ((X16) = (X17)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t56_mcart_1])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.68/0.88            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.88          | ((sk_A) = (X3))
% 0.68/0.88          | ((sk_A) = (k1_xboole_0))
% 0.68/0.88          | ((sk_B) = (k1_xboole_0))
% 0.68/0.88          | ((sk_C) = (k1_xboole_0))
% 0.68/0.88          | ((sk_D) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      ((((sk_D) = (k1_xboole_0))
% 0.68/0.88        | ((sk_C) = (k1_xboole_0))
% 0.68/0.88        | ((sk_B) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('eq_res', [status(thm)], ['10'])).
% 0.68/0.88  thf(d4_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.88     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.68/0.88       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf(t113_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X1 : $i, X2 : $i]:
% 0.68/0.88         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0))
% 0.68/0.88          | ((sk_A) = (sk_E))
% 0.68/0.88          | ((sk_A) = (k1_xboole_0))
% 0.68/0.88          | ((sk_B) = (k1_xboole_0))
% 0.68/0.88          | ((sk_C) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['11', '15'])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_C) = (k1_xboole_0))
% 0.68/0.88        | ((sk_B) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['7', '16'])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      ((((sk_C) = (k1_xboole_0))
% 0.68/0.88        | ((sk_B) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.68/0.88  thf(t35_mcart_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.68/0.88         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.68/0.88       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.68/0.88         (((X12) != (k1_xboole_0))
% 0.68/0.88          | ((k3_zfmisc_1 @ X9 @ X10 @ X12) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i]:
% 0.68/0.88         ((k3_zfmisc_1 @ X9 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['20'])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.68/0.88           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X1 : $i, X2 : $i]:
% 0.68/0.88         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['23', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_A) = (sk_E))
% 0.68/0.88          | ((sk_A) = (k1_xboole_0))
% 0.68/0.88          | ((sk_B) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['19', '26'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_B) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['6', '27'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.68/0.88         (((X10) != (k1_xboole_0))
% 0.68/0.88          | ((k3_zfmisc_1 @ X9 @ X10 @ X12) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X9 : $i, X12 : $i]:
% 0.68/0.88         ((k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 0.68/0.88           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_A) = (sk_E))
% 0.68/0.88          | ((sk_A) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['30', '36'])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['5', '37'])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('40', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.68/0.88         (((X9) != (k1_xboole_0))
% 0.68/0.88          | ((k3_zfmisc_1 @ X9 @ X10 @ X12) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X10 : $i, X12 : $i]:
% 0.68/0.88         ((k3_zfmisc_1 @ k1_xboole_0 @ X10 @ X12) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 0.68/0.88           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['40', '46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (sk_E)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['4', '47'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('50', plain, (((sk_A) = (sk_E))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['3', '50'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['3', '50'])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.68/0.88         X20 : $i]:
% 0.68/0.88         (((X13) = (k1_xboole_0))
% 0.68/0.88          | ((X14) = (k1_xboole_0))
% 0.68/0.88          | ((X15) = (k1_xboole_0))
% 0.68/0.88          | ((X16) = (k1_xboole_0))
% 0.68/0.88          | ((k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13)
% 0.68/0.88              != (k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20))
% 0.68/0.88          | ((X15) = (X18)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t56_mcart_1])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.88            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.68/0.88          | ((X2) = (sk_B))
% 0.68/0.88          | ((X3) = (k1_xboole_0))
% 0.68/0.88          | ((X2) = (k1_xboole_0))
% 0.68/0.88          | ((X1) = (k1_xboole_0))
% 0.68/0.88          | ((X0) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      ((((sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('eq_res', [status(thm)], ['55'])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (sk_B))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['56', '57'])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      ((((sk_F) = (sk_B))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['60'])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['23', '25'])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (k1_xboole_0))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['61', '62'])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (sk_B))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)) | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['65'])).
% 0.68/0.88  thf('67', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (sk_B))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['66', '67'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['68', '69'])).
% 0.68/0.88  thf('71', plain, ((((sk_F) = (sk_B)) | ((sk_E) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['70'])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['71', '72'])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (sk_B)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['52', '73'])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('76', plain, (((sk_F) = (sk_B))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['51', '76'])).
% 0.68/0.88  thf('78', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['51', '76'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['51', '76'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.68/0.88         X20 : $i]:
% 0.68/0.88         (((X13) = (k1_xboole_0))
% 0.68/0.88          | ((X14) = (k1_xboole_0))
% 0.68/0.88          | ((X15) = (k1_xboole_0))
% 0.68/0.88          | ((X16) = (k1_xboole_0))
% 0.68/0.88          | ((k4_zfmisc_1 @ X16 @ X15 @ X14 @ X13)
% 0.68/0.88              != (k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20))
% 0.68/0.88          | ((X14) = (X19)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t56_mcart_1])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.88            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.68/0.88          | ((X1) = (sk_C))
% 0.68/0.88          | ((X3) = (k1_xboole_0))
% 0.68/0.88          | ((X2) = (k1_xboole_0))
% 0.68/0.88          | ((X1) = (k1_xboole_0))
% 0.68/0.88          | ((X0) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['80', '81'])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      ((((sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('eq_res', [status(thm)], ['82'])).
% 0.68/0.88  thf('84', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (sk_C))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['83', '84'])).
% 0.68/0.88  thf('86', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('87', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['85', '86'])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      ((((sk_G) = (sk_C))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['87'])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['23', '25'])).
% 0.68/0.88  thf('90', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_F) = (k1_xboole_0))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['88', '89'])).
% 0.68/0.88  thf('91', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('92', plain,
% 0.68/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (sk_C))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_F) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['90', '91'])).
% 0.68/0.88  thf('93', plain,
% 0.68/0.88      ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)) | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['92'])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (sk_C))
% 0.68/0.88          | ((sk_E) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['93', '94'])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_E) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['79', '95'])).
% 0.68/0.88  thf('97', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('98', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.68/0.88  thf('99', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['98', '99'])).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_G) = (sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['78', '100'])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('103', plain, (((sk_G) = (sk_C))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['77', '103'])).
% 0.68/0.88  thf('105', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['77', '103'])).
% 0.68/0.88  thf('106', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D)
% 0.68/0.88         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['51', '76'])).
% 0.68/0.88  thf('107', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf(t195_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.68/0.88          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.68/0.88               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.68/0.88  thf('108', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]:
% 0.68/0.88         (((X3) = (k1_xboole_0))
% 0.68/0.88          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.68/0.88          | ((X4) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.68/0.88  thf('109', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.68/0.88          | ((X0) = (k1_xboole_0))
% 0.68/0.88          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['107', '108'])).
% 0.68/0.88  thf('110', plain,
% 0.68/0.88      ((((k2_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)) = (sk_D))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_C) = (k1_xboole_0))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('111', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.68/0.88          | ((X0) = (k1_xboole_0))
% 0.68/0.88          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['107', '108'])).
% 0.68/0.88  thf('112', plain,
% 0.68/0.88      ((((sk_D) = (sk_H))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_C) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['110', '111'])).
% 0.68/0.88  thf('113', plain, (((sk_G) = (sk_C))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.68/0.88  thf('114', plain,
% 0.68/0.88      ((((sk_D) = (sk_H))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['112', '113'])).
% 0.68/0.88  thf('115', plain,
% 0.68/0.88      ((((sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0))
% 0.68/0.88        | ((sk_D) = (sk_H)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['114'])).
% 0.68/0.88  thf('116', plain,
% 0.68/0.88      ((((sk_A) != (sk_E))
% 0.68/0.88        | ((sk_B) != (sk_F))
% 0.68/0.88        | ((sk_C) != (sk_G))
% 0.68/0.88        | ((sk_D) != (sk_H)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('117', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.68/0.88      inference('split', [status(esa)], ['116'])).
% 0.68/0.88  thf('118', plain, (((sk_F) = (sk_B))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.68/0.88  thf('119', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.68/0.88      inference('split', [status(esa)], ['116'])).
% 0.68/0.88  thf('120', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['118', '119'])).
% 0.68/0.88  thf('121', plain, ((((sk_B) = (sk_F)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['120'])).
% 0.68/0.88  thf('122', plain, (((sk_A) = (sk_E))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('123', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.68/0.88      inference('split', [status(esa)], ['116'])).
% 0.68/0.88  thf('124', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['122', '123'])).
% 0.68/0.88  thf('125', plain, ((((sk_A) = (sk_E)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['124'])).
% 0.68/0.88  thf('126', plain, (((sk_G) = (sk_C))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.68/0.88  thf('127', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.68/0.88      inference('split', [status(esa)], ['116'])).
% 0.68/0.88  thf('128', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['126', '127'])).
% 0.68/0.88  thf('129', plain, ((((sk_C) = (sk_G)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['128'])).
% 0.68/0.88  thf('130', plain,
% 0.68/0.88      (~ (((sk_D) = (sk_H))) | ~ (((sk_C) = (sk_G))) | ~ (((sk_A) = (sk_E))) | 
% 0.68/0.88       ~ (((sk_B) = (sk_F)))),
% 0.68/0.88      inference('split', [status(esa)], ['116'])).
% 0.68/0.88  thf('131', plain, (~ (((sk_D) = (sk_H)))),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['121', '125', '129', '130'])).
% 0.68/0.88  thf('132', plain, (((sk_D) != (sk_H))),
% 0.68/0.88      inference('simpl_trail', [status(thm)], ['117', '131'])).
% 0.68/0.88  thf('133', plain,
% 0.68/0.88      ((((sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['115', '132'])).
% 0.68/0.88  thf('134', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.68/0.88           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.68/0.88  thf('135', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 0.68/0.88            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.68/0.88          | ((sk_D) = (k1_xboole_0))
% 0.68/0.88          | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['133', '134'])).
% 0.68/0.88  thf('136', plain,
% 0.68/0.88      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.88  thf('137', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0))
% 0.68/0.88          | ((sk_D) = (k1_xboole_0))
% 0.68/0.88          | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['135', '136'])).
% 0.68/0.88  thf('138', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_D) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['105', '137'])).
% 0.68/0.88  thf('139', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('140', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 0.68/0.88  thf('141', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('142', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) = (k1_xboole_0))
% 0.68/0.88          | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['140', '141'])).
% 0.68/0.88  thf('143', plain,
% 0.68/0.88      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.68/0.88        | ((sk_H) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['104', '142'])).
% 0.68/0.88  thf('144', plain,
% 0.68/0.88      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('145', plain, (((sk_H) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 0.68/0.88  thf('146', plain, (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['2', '145'])).
% 0.68/0.88  thf('147', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('148', plain, (((sk_H) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 0.68/0.88  thf('149', plain, (((sk_H) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 0.68/0.88  thf('150', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.68/0.88  thf('151', plain, (((sk_H) != (sk_H))),
% 0.68/0.88      inference('demod', [status(thm)], ['146', '150'])).
% 0.68/0.88  thf('152', plain, ($false), inference('simplify', [status(thm)], ['151'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
