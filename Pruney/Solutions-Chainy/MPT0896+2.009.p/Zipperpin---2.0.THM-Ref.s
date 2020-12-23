%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYVR3l7CeM

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:40 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  162 (3247 expanded)
%              Number of leaves         :   18 ( 950 expanded)
%              Depth                    :   41
%              Number of atoms          : 1646 (46643 expanded)
%              Number of equality atoms :  324 (9147 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ( X0 = X3 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X11 @ X12 @ X14 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( X11 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X11 @ X12 @ X14 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('26',plain,(
    ! [X12: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X12 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) @ X3 ) ) ),
    inference(demod,[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('42',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','61'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','70'])).

thf('72',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(eq_res,[status(thm)],['71'])).

thf('73',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','61'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('83',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X5 = X1 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','61'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(eq_res,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','100'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','101'])).

thf('103',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['97','98','99'])).

thf('111',plain,(
    sk_G != k1_xboole_0 ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['106','107','108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ( X0 = X3 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_B = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['114','115','116'])).

thf('118',plain,(
    sk_B = sk_F ),
    inference(eq_res,[status(thm)],['117'])).

thf('119',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['58','59','60'])).

thf('122',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['119'])).

thf('123',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['97','98','99'])).

thf('126',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['119'])).

thf('127',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['106','107','108','111'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_A = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['131','132','133'])).

thf('135',plain,(
    sk_A = sk_E ),
    inference(eq_res,[status(thm)],['134'])).

thf('136',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['119'])).

thf('137',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['119'])).

thf('140',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['124','128','138','139'])).

thf('141',plain,(
    sk_B != sk_F ),
    inference(simpl_trail,[status(thm)],['120','140'])).

thf('142',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYVR3l7CeM
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.49/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.73  % Solved by: fo/fo7.sh
% 0.49/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.73  % done 611 iterations in 0.260s
% 0.49/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.73  % SZS output start Refutation
% 0.49/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.73  thf(sk_H_type, type, sk_H: $i).
% 0.49/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.73  thf(sk_G_type, type, sk_G: $i).
% 0.49/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.73  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.49/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.49/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.49/0.73  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.49/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.73  thf(d3_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.49/0.73       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.49/0.73  thf('0', plain,
% 0.49/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.49/0.73           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.73  thf('1', plain,
% 0.49/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.49/0.73           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.73  thf('2', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.49/0.73      inference('sup+', [status(thm)], ['0', '1'])).
% 0.49/0.73  thf(d4_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.73     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.49/0.73       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.49/0.73  thf('3', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf('4', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf(t56_mcart_1, conjecture,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.49/0.73     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.49/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.49/0.73           ( ( D ) = ( H ) ) ) ) ))).
% 0.49/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.73    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.49/0.73        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.49/0.73          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.49/0.73              ( ( D ) = ( H ) ) ) ) ) )),
% 0.49/0.73    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.49/0.73  thf('5', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('6', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf('7', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('8', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf(t134_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.49/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.49/0.73  thf('9', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ X2 @ X3))
% 0.49/0.73          | ((X0) = (X3)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.49/0.73  thf('10', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((X4) = (X0))
% 0.49/0.73          | ((X5) = (k1_xboole_0))
% 0.49/0.73          | ((X4) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.73  thf('11', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.49/0.73          | ((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((X0) = (sk_D)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.49/0.73  thf('12', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.49/0.73            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.49/0.73          | ((X0) = (sk_D))
% 0.49/0.73          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.49/0.73          | ((X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['6', '11'])).
% 0.49/0.73  thf('13', plain,
% 0.49/0.73      ((((sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('eq_res', [status(thm)], ['12'])).
% 0.49/0.73  thf('14', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf('15', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 0.49/0.73            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.49/0.73          | ((sk_H) = (sk_D))
% 0.49/0.73          | ((sk_H) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.49/0.73  thf('16', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf(t35_mcart_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.73         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.49/0.73       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.49/0.73  thf('17', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.49/0.73         (((X14) != (k1_xboole_0))
% 0.49/0.73          | ((k3_zfmisc_1 @ X11 @ X12 @ X14) = (k1_xboole_0)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.49/0.73  thf('18', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ X11 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.49/0.73  thf('19', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['16', '18'])).
% 0.49/0.73  thf('20', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ X11 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.49/0.73  thf('21', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf('22', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.49/0.73           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.73  thf('23', plain,
% 0.49/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.49/0.73           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.49/0.73  thf('24', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X3)
% 0.49/0.73           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) @ X3))),
% 0.49/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.49/0.73  thf('25', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.49/0.73         (((X11) != (k1_xboole_0))
% 0.49/0.73          | ((k3_zfmisc_1 @ X11 @ X12 @ X14) = (k1_xboole_0)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.49/0.73  thf('26', plain,
% 0.49/0.73      (![X12 : $i, X14 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ k1_xboole_0 @ X12 @ X14) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.49/0.73  thf('27', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k1_xboole_0)
% 0.49/0.73           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['24', '26'])).
% 0.49/0.73  thf('28', plain,
% 0.49/0.73      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['19', '27'])).
% 0.49/0.73  thf('29', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0))
% 0.49/0.73          | ((sk_H) = (k1_xboole_0))
% 0.49/0.73          | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['15', '28'])).
% 0.49/0.73  thf('30', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('31', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('32', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.73         (((k3_zfmisc_1 @ X11 @ X12 @ X13) != (k1_xboole_0))
% 0.49/0.73          | ((X13) = (k1_xboole_0))
% 0.49/0.73          | ((X12) = (k1_xboole_0))
% 0.49/0.73          | ((X11) = (k1_xboole_0)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.49/0.73  thf('33', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.73  thf('34', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((sk_D) = (k1_xboole_0))
% 0.49/0.73        | ((sk_C) = (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['30', '33'])).
% 0.49/0.73  thf('35', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('36', plain, (((sk_D) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('37', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.49/0.73  thf('38', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D))
% 0.49/0.73        | ((sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['29', '37'])).
% 0.49/0.73  thf('39', plain,
% 0.49/0.73      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['38'])).
% 0.49/0.73  thf('40', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['16', '18'])).
% 0.49/0.73  thf('41', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.49/0.73           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.73  thf('42', plain,
% 0.49/0.73      (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['40', '41'])).
% 0.49/0.73  thf('43', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ X2 @ X3))
% 0.49/0.73          | ((X1) = (X2)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.49/0.73  thf('44', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.73  thf('45', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.73  thf('46', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D))
% 0.49/0.73        | ((sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['39', '45'])).
% 0.49/0.73  thf('47', plain,
% 0.49/0.73      ((((sk_B) = (k1_xboole_0))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.49/0.73  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('50', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['47', '48', '49'])).
% 0.49/0.73  thf('51', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['16', '18'])).
% 0.49/0.73  thf('52', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.49/0.73          | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.49/0.73  thf('53', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.49/0.73  thf('54', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.73  thf('55', plain,
% 0.49/0.73      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['54'])).
% 0.49/0.73  thf('56', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.73  thf('57', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_H) = (sk_D))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.73  thf('58', plain,
% 0.49/0.73      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['57'])).
% 0.49/0.73  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('61', plain, (((sk_H) = (sk_D))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['58', '59', '60'])).
% 0.49/0.73  thf('62', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('demod', [status(thm)], ['5', '61'])).
% 0.49/0.73  thf('63', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf(t37_mcart_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.73     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.49/0.73       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.49/0.73  thf('64', plain,
% 0.49/0.73      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.73         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.49/0.73          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.49/0.73          | ((X15) = (X18)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.49/0.73  thf('65', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.49/0.73          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.49/0.73          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.49/0.73  thf('66', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('67', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.49/0.73          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.49/0.73          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.73  thf('68', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.49/0.73            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['62', '67'])).
% 0.49/0.73  thf('69', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('demod', [status(thm)], ['5', '61'])).
% 0.49/0.73  thf('70', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.49/0.73            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.49/0.73      inference('demod', [status(thm)], ['68', '69'])).
% 0.49/0.73  thf('71', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.49/0.73            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2))
% 0.49/0.73          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['4', '70'])).
% 0.49/0.73  thf('72', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.49/0.73      inference('eq_res', [status(thm)], ['71'])).
% 0.49/0.73  thf('73', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('74', plain,
% 0.49/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.73           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.49/0.73  thf('75', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.73  thf('76', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.49/0.73          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.49/0.73          | ((X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.49/0.73  thf('77', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((sk_D) = (k1_xboole_0))
% 0.49/0.73        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['73', '76'])).
% 0.49/0.73  thf('78', plain, (((sk_D) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('79', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.49/0.73  thf('80', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('demod', [status(thm)], ['5', '61'])).
% 0.49/0.73  thf('81', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('82', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('83', plain,
% 0.49/0.73      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.73         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.49/0.73          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.49/0.73          | ((X16) = (X19)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.49/0.73  thf('84', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((X5) = (X1))
% 0.49/0.73          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['82', '83'])).
% 0.49/0.73  thf('85', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.49/0.73            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.49/0.73          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (X5)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['81', '84'])).
% 0.49/0.73  thf('86', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.49/0.73           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.49/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('87', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.49/0.73            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.49/0.73          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (X5)))),
% 0.49/0.73      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.73  thf('88', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.49/0.73            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((sk_C) = (X1))
% 0.49/0.73          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['80', '87'])).
% 0.49/0.73  thf('89', plain,
% 0.49/0.73      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.49/0.73         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.49/0.73      inference('demod', [status(thm)], ['5', '61'])).
% 0.49/0.73  thf('90', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.49/0.73            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.49/0.73          | ((sk_C) = (X1))
% 0.49/0.73          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['88', '89'])).
% 0.49/0.73  thf('91', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.49/0.73        | ((sk_C) = (sk_G)))),
% 0.49/0.73      inference('eq_res', [status(thm)], ['90'])).
% 0.49/0.73  thf('92', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.49/0.73  thf('93', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_C) = (sk_G))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.73  thf('94', plain,
% 0.49/0.73      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['93'])).
% 0.49/0.73  thf('95', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.73  thf('96', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((sk_C) = (sk_G))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['94', '95'])).
% 0.49/0.73  thf('97', plain,
% 0.49/0.73      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['96'])).
% 0.49/0.73  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('99', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('100', plain, (((sk_C) = (sk_G))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['97', '98', '99'])).
% 0.49/0.73  thf('101', plain,
% 0.49/0.73      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.49/0.73        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['79', '100'])).
% 0.49/0.73  thf('102', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.49/0.73        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['72', '101'])).
% 0.49/0.73  thf('103', plain,
% 0.49/0.73      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['102'])).
% 0.49/0.73  thf('104', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.73         (((k3_zfmisc_1 @ X11 @ X12 @ X13) != (k1_xboole_0))
% 0.49/0.73          | ((X13) = (k1_xboole_0))
% 0.49/0.73          | ((X12) = (k1_xboole_0))
% 0.49/0.73          | ((X11) = (k1_xboole_0)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.49/0.73  thf('105', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((sk_B) = (k1_xboole_0))
% 0.49/0.73        | ((sk_G) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['103', '104'])).
% 0.49/0.73  thf('106', plain,
% 0.49/0.73      ((((sk_G) = (k1_xboole_0))
% 0.49/0.73        | ((sk_B) = (k1_xboole_0))
% 0.49/0.73        | ((sk_A) = (k1_xboole_0))
% 0.49/0.73        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['105'])).
% 0.49/0.73  thf('107', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('109', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('110', plain, (((sk_C) = (sk_G))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['97', '98', '99'])).
% 0.49/0.73  thf('111', plain, (((sk_G) != (k1_xboole_0))),
% 0.49/0.73      inference('demod', [status(thm)], ['109', '110'])).
% 0.49/0.73  thf('112', plain,
% 0.49/0.73      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)],
% 0.49/0.73                ['106', '107', '108', '111'])).
% 0.49/0.73  thf('113', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ X2 @ X3))
% 0.49/0.73          | ((X0) = (X3)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.49/0.73  thf('114', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.73          | ((sk_B) = (X0))
% 0.49/0.73          | ((sk_A) = (k1_xboole_0))
% 0.49/0.73          | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['112', '113'])).
% 0.49/0.73  thf('115', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('116', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('117', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.73          | ((sk_B) = (X0)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['114', '115', '116'])).
% 0.49/0.73  thf('118', plain, (((sk_B) = (sk_F))),
% 0.49/0.73      inference('eq_res', [status(thm)], ['117'])).
% 0.49/0.73  thf('119', plain,
% 0.49/0.73      ((((sk_A) != (sk_E))
% 0.49/0.73        | ((sk_B) != (sk_F))
% 0.49/0.73        | ((sk_C) != (sk_G))
% 0.49/0.73        | ((sk_D) != (sk_H)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('120', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.49/0.73      inference('split', [status(esa)], ['119'])).
% 0.49/0.73  thf('121', plain, (((sk_H) = (sk_D))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['58', '59', '60'])).
% 0.49/0.73  thf('122', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.49/0.73      inference('split', [status(esa)], ['119'])).
% 0.49/0.73  thf('123', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['121', '122'])).
% 0.49/0.73  thf('124', plain, ((((sk_D) = (sk_H)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.73  thf('125', plain, (((sk_C) = (sk_G))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['97', '98', '99'])).
% 0.49/0.73  thf('126', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.49/0.73      inference('split', [status(esa)], ['119'])).
% 0.49/0.73  thf('127', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['125', '126'])).
% 0.49/0.73  thf('128', plain, ((((sk_C) = (sk_G)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['127'])).
% 0.49/0.73  thf('129', plain,
% 0.49/0.73      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)],
% 0.49/0.73                ['106', '107', '108', '111'])).
% 0.49/0.73  thf('130', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.73         (((X0) = (k1_xboole_0))
% 0.49/0.73          | ((X1) = (k1_xboole_0))
% 0.49/0.73          | ((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ X2 @ X3))
% 0.49/0.73          | ((X1) = (X2)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.49/0.73  thf('131', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.73          | ((sk_A) = (X1))
% 0.49/0.73          | ((sk_A) = (k1_xboole_0))
% 0.49/0.73          | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['129', '130'])).
% 0.49/0.73  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('133', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('134', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.73          | ((sk_A) = (X1)))),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['131', '132', '133'])).
% 0.49/0.73  thf('135', plain, (((sk_A) = (sk_E))),
% 0.49/0.73      inference('eq_res', [status(thm)], ['134'])).
% 0.49/0.73  thf('136', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.49/0.73      inference('split', [status(esa)], ['119'])).
% 0.49/0.73  thf('137', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['135', '136'])).
% 0.49/0.73  thf('138', plain, ((((sk_A) = (sk_E)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['137'])).
% 0.49/0.73  thf('139', plain,
% 0.49/0.73      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.49/0.73       ~ (((sk_D) = (sk_H)))),
% 0.49/0.73      inference('split', [status(esa)], ['119'])).
% 0.49/0.73  thf('140', plain, (~ (((sk_B) = (sk_F)))),
% 0.49/0.73      inference('sat_resolution*', [status(thm)], ['124', '128', '138', '139'])).
% 0.49/0.73  thf('141', plain, (((sk_B) != (sk_F))),
% 0.49/0.73      inference('simpl_trail', [status(thm)], ['120', '140'])).
% 0.49/0.73  thf('142', plain, ($false),
% 0.49/0.73      inference('simplify_reflect-', [status(thm)], ['118', '141'])).
% 0.49/0.73  
% 0.49/0.73  % SZS output end Refutation
% 0.49/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
