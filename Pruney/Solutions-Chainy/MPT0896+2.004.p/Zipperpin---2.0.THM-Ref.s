%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IdUVgfJV1A

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:39 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 705 expanded)
%              Number of leaves         :   19 ( 210 expanded)
%              Depth                    :   26
%              Number of atoms          : 1122 (12844 expanded)
%              Number of equality atoms :  212 (2948 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t56_mcart_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_mcart_1])).

thf('5',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('21',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','34'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_B = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51'])).

thf('53',plain,(
    sk_B = sk_F ),
    inference(eq_res,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['33'])).

thf('57',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['54'])).

thf('58',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('61',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','34'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','34'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['54'])).

thf('75',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_A = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81'])).

thf('83',plain,(
    sk_A = sk_E ),
    inference(eq_res,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['54'])).

thf('85',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['54'])).

thf('88',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['59','76','86','87'])).

thf('89',plain,(
    sk_B != sk_F ),
    inference(simpl_trail,[status(thm)],['55','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IdUVgfJV1A
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 403 iterations in 0.183s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(sk_H_type, type, sk_H: $i).
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.64  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.47/0.64  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(d3_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.47/0.64       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.47/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf(d4_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.47/0.64       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf(t56_mcart_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.47/0.64     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.47/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.47/0.64           ( ( D ) = ( H ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.47/0.64        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.47/0.64          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.47/0.64              ( ( D ) = ( H ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.64  thf(t134_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.47/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((X3) = (k1_xboole_0))
% 0.47/0.64          | ((X4) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.64          | ((X3) = (X6)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.64          | ((X4) = (X0))
% 0.47/0.64          | ((X5) = (k1_xboole_0))
% 0.47/0.64          | ((X4) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.47/0.64          | ((X0) = (k1_xboole_0))
% 0.47/0.64          | ((X1) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['7', '10'])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.47/0.64            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.47/0.64          | ((X0) = (sk_D))
% 0.47/0.64          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['6', '11'])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      ((((sk_H) = (k1_xboole_0))
% 0.47/0.64        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.47/0.64        | ((sk_H) = (sk_D)))),
% 0.47/0.64      inference('eq_res', [status(thm)], ['12'])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 0.47/0.64            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.47/0.64          | ((sk_H) = (sk_D))
% 0.47/0.64          | ((sk_H) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.64  thf(t113_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((sk_H) = (sk_D))
% 0.47/0.64          | ((sk_H) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t55_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.47/0.64       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 0.47/0.64          | ((X23) = (k1_xboole_0))
% 0.47/0.64          | ((X22) = (k1_xboole_0))
% 0.47/0.64          | ((X21) = (k1_xboole_0))
% 0.47/0.64          | ((X20) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.47/0.64        | ((sk_A) = (k1_xboole_0))
% 0.47/0.64        | ((sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.64  thf('22', plain, (((sk_D) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)],
% 0.47/0.64                ['21', '22', '23', '24', '25'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64        | ((sk_H) = (k1_xboole_0))
% 0.47/0.64        | ((sk_H) = (sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '26'])).
% 0.47/0.64  thf('28', plain, ((((sk_H) = (sk_D)) | ((sk_H) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.47/0.64         (((X24) != (k1_xboole_0))
% 0.47/0.64          | ((k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.64         ((k4_zfmisc_1 @ X20 @ X21 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.47/0.64          | ((sk_H) = (sk_D)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['28', '30'])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)],
% 0.47/0.64                ['21', '22', '23', '24', '25'])).
% 0.47/0.64  thf('33', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.64  thf('34', plain, (((sk_H) = (sk_D))),
% 0.47/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('demod', [status(thm)], ['5', '34'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf(t37_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.64     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.47/0.64       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.64         (((k3_zfmisc_1 @ X14 @ X15 @ X16) = (k1_xboole_0))
% 0.47/0.64          | ((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.47/0.64          | ((X14) = (X17)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.47/0.64          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.47/0.64          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.47/0.64          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.47/0.64          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.64            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.64          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['35', '40'])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('demod', [status(thm)], ['5', '34'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.64            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.64          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.47/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)],
% 0.47/0.64                ['21', '22', '23', '24', '25'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.64            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.64          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.64            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.64          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '45'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.47/0.64      inference('eq_res', [status(thm)], ['46'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((X3) = (k1_xboole_0))
% 0.47/0.64          | ((X4) = (k1_xboole_0))
% 0.47/0.64          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.64          | ((X3) = (X6)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.64          | ((sk_B) = (X0))
% 0.47/0.64          | ((sk_A) = (k1_xboole_0))
% 0.47/0.64          | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.64  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.64          | ((sk_B) = (X0)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['49', '50', '51'])).
% 0.47/0.64  thf('53', plain, (((sk_B) = (sk_F))),
% 0.47/0.64      inference('eq_res', [status(thm)], ['52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      ((((sk_A) != (sk_E))
% 0.47/0.64        | ((sk_B) != (sk_F))
% 0.47/0.64        | ((sk_C) != (sk_G))
% 0.47/0.64        | ((sk_D) != (sk_H)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('55', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.47/0.64      inference('split', [status(esa)], ['54'])).
% 0.47/0.64  thf('56', plain, (((sk_H) = (sk_D))),
% 0.47/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.64  thf('57', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.47/0.64      inference('split', [status(esa)], ['54'])).
% 0.47/0.64  thf('58', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.64  thf('59', plain, ((((sk_D) = (sk_H)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.47/0.64         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.64      inference('demod', [status(thm)], ['5', '34'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.64         (((k3_zfmisc_1 @ X14 @ X15 @ X16) = (k1_xboole_0))
% 0.47/0.64          | ((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.47/0.64          | ((X15) = (X18)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.47/0.64          | ((X1) = (X5))
% 0.47/0.64          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.64         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.47/0.64          | ((X1) = (X5))
% 0.47/0.64          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.65            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['61', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.47/0.65         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.65      inference('demod', [status(thm)], ['5', '34'])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.65            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (X1)))),
% 0.47/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)],
% 0.47/0.65                ['21', '22', '23', '24', '25'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.65            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((sk_C) = (X1)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.65            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((sk_C) = (X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['60', '71'])).
% 0.47/0.65  thf('73', plain, (((sk_C) = (sk_G))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['72'])).
% 0.47/0.65  thf('74', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.47/0.65      inference('split', [status(esa)], ['54'])).
% 0.47/0.65  thf('75', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.47/0.65  thf('76', plain, ((((sk_C) = (sk_G)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['75'])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['46'])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X4) = (X5)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((sk_A) = (X1))
% 0.47/0.65          | ((sk_A) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.47/0.65  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((sk_A) = (X1)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['79', '80', '81'])).
% 0.47/0.65  thf('83', plain, (((sk_A) = (sk_E))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['82'])).
% 0.47/0.65  thf('84', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.47/0.65      inference('split', [status(esa)], ['54'])).
% 0.47/0.65  thf('85', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['83', '84'])).
% 0.47/0.65  thf('86', plain, ((((sk_A) = (sk_E)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['85'])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.47/0.65       ~ (((sk_D) = (sk_H)))),
% 0.47/0.65      inference('split', [status(esa)], ['54'])).
% 0.47/0.65  thf('88', plain, (~ (((sk_B) = (sk_F)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['59', '76', '86', '87'])).
% 0.47/0.65  thf('89', plain, (((sk_B) != (sk_F))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['55', '88'])).
% 0.47/0.65  thf('90', plain, ($false),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['53', '89'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
