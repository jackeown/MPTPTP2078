%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0897+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfGwBYoFZC

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:40 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  160 (20271 expanded)
%              Number of leaves         :   13 (5062 expanded)
%              Depth                    :   51
%              Number of atoms          : 1674 (375934 expanded)
%              Number of equality atoms :  379 (76043 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X8 = X9 ) ) ),
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

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X4 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X2 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['6','20'])).

thf('22',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X1 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ k1_xboole_0 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['4','32'])).

thf('34',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('35',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('37',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('38',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('39',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('40',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('41',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X2 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(eq_res,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['39','51'])).

thf('53',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ k1_xboole_0 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['38','56'])).

thf('58',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('59',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['37','61'])).

thf('63',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('64',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['36','64'])).

thf('66',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['36','64'])).

thf('67',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['36','64'])).

thf('68',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X6 = X11 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X1 = sk_C )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference(eq_res,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_G = sk_C )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_G = sk_C )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_G = sk_C ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = sk_C )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ k1_xboole_0 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_G = sk_C )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup+',[status(thm)],['67','83'])).

thf('85',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('86',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_G = sk_C ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_G = sk_C ) ),
    inference('sup+',[status(thm)],['66','88'])).

thf('90',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('91',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['65','91'])).

thf('93',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['65','91'])).

thf('94',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('95',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X5 = X12 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_D = X0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(eq_res,[status(thm)],['96'])).

thf('98',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('99',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X5 = X12 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_H = sk_D )
    | ( sk_D = sk_H )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','101'])).

thf('103',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( sk_C != sk_G )
    | ( sk_H = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['103'])).

thf('105',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('106',plain,
    ( ( sk_C != sk_G )
    | ( sk_H = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_C != sk_G ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('109',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G != sk_G ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_H = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('114',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['111'])).

thf('115',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('118',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['111'])).

thf('119',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    sk_G = sk_C ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('122',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['111'])).

thf('123',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( sk_D != sk_H )
    | ( sk_C != sk_G )
    | ( sk_A != sk_E )
    | ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['111'])).

thf('126',plain,(
    sk_D != sk_H ),
    inference('sat_resolution*',[status(thm)],['116','120','124','125'])).

thf('127',plain,(
    sk_D != sk_H ),
    inference(simpl_trail,[status(thm)],['112','126'])).

thf('128',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['110','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','130'])).

thf('132',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('133',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X0 @ k1_xboole_0 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','135'])).

thf('137',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('138',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('139',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != sk_E ),
    inference(demod,[status(thm)],['2','138'])).

thf('140',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('141',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('142',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('143',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ sk_E @ X1 @ X2 @ X4 )
      = sk_E ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['139','143'])).

thf('145',plain,(
    $false ),
    inference(simplify,[status(thm)],['144'])).


%------------------------------------------------------------------------------
