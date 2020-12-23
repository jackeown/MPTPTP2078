%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0896+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GM4SS0v4eG

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:40 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 666 expanded)
%              Number of leaves         :   17 ( 195 expanded)
%              Depth                    :   25
%              Number of atoms          : 1084 (13480 expanded)
%              Number of equality atoms :  250 (3176 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

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

thf('1',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = X5 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['8'])).

thf(t36_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X14 @ X13 @ X12 )
       != ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) )
      | ( X14 = X15 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_A = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_A = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X14 @ X13 @ X12 )
       != ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_B = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_B = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X14 @ X13 @ X12 )
       != ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) )
      | ( X12 = X17 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( sk_C = sk_G )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( sk_B = X1 ) ) ),
    inference(demod,[status(thm)],['22','37'])).

thf('39',plain,
    ( ( sk_B = sk_F )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('47',plain,(
    sk_G != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','47'])).

thf('49',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_A = X2 ) ) ),
    inference(demod,[status(thm)],['15','48','49'])).

thf('51',plain,
    ( ( sk_A = sk_E )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_F @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('55',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( X0 = X4 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_D = X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(eq_res,[status(thm)],['62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_D = sk_H ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['52'])).

thf('72',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('75',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['52'])).

thf('76',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','47'])).

thf('79',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('80',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['52'])).

thf('83',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['73','77','81','82'])).

thf('84',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['53','83'])).

thf('85',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_F @ sk_G )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['51','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','47'])).

thf('92',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_G != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','89','92','93'])).


%------------------------------------------------------------------------------
