%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pu1GZOfYV7

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:40 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  245 (68164 expanded)
%              Number of leaves         :   17 (19348 expanded)
%              Depth                    :   89
%              Number of atoms          : 2729 (1013163 expanded)
%              Number of equality atoms :  571 (173906 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('5',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D @ X0 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D @ X0 )
      = ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('24',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_H @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_H = sk_D ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('51',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','51'])).

thf('53',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','51'])).

thf('54',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','51'])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('56',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','51'])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = X5 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = X0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = X3 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
        = ( k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','80'])).

thf('82',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('85',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','91'])).

thf('93',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('94',plain,
    ( ( sk_C = sk_G )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_H @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['3','51'])).

thf('101',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('103',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['52','103'])).

thf('105',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['52','103'])).

thf('106',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['52','103'])).

thf('107',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['61'])).

thf('108',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('109',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('110',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('113',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = X4 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['116'])).

thf('118',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('128',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('131',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['129','134'])).

thf('136',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','135'])).

thf('137',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('138',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('140',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['138','143'])).

thf('145',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','144'])).

thf('146',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('147',plain,
    ( ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_H @ X0 )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( sk_G = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( sk_A = sk_E )
    | ( sk_G = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_G )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['52','103'])).

thf('162',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_A = sk_E ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('164',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k4_zfmisc_1 @ sk_E @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['104','164'])).

thf('166',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['116'])).

thf('167',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('168',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('169',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('170',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_B = X0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['172'])).

thf('174',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['174'])).

thf('176',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('177',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['174'])).

thf('178',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('181',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['174'])).

thf('182',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('185',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['174'])).

thf('186',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['174'])).

thf('189',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['179','183','187','188'])).

thf('190',plain,(
    sk_B != sk_F ),
    inference(simpl_trail,[status(thm)],['175','189'])).

thf('191',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['173','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('193',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('196',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('199',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['165','202'])).

thf('204',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('205',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_H @ X0 )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_G )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0 )
       != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    sk_E = k1_xboole_0 ),
    inference(condensation,[status(thm)],['218'])).

thf('220',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != sk_E ),
    inference(demod,[status(thm)],['2','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('222',plain,(
    sk_E = k1_xboole_0 ),
    inference(condensation,[status(thm)],['218'])).

thf('223',plain,(
    sk_E = k1_xboole_0 ),
    inference(condensation,[status(thm)],['218'])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['220','224'])).

thf('226',plain,(
    $false ),
    inference(simplify,[status(thm)],['225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pu1GZOfYV7
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.75/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.95  % Solved by: fo/fo7.sh
% 1.75/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.95  % done 2249 iterations in 1.514s
% 1.75/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.95  % SZS output start Refutation
% 1.75/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.75/1.95  thf(sk_H_type, type, sk_H: $i).
% 1.75/1.95  thf(sk_G_type, type, sk_G: $i).
% 1.75/1.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.95  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.75/1.95  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.75/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.95  thf(sk_F_type, type, sk_F: $i).
% 1.75/1.95  thf(sk_E_type, type, sk_E: $i).
% 1.75/1.95  thf(sk_D_type, type, sk_D: $i).
% 1.75/1.95  thf(t57_mcart_1, conjecture,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.75/1.95     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.75/1.95       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.75/1.95         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.75/1.95           ( ( D ) = ( H ) ) ) ) ))).
% 1.75/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.95    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.75/1.95        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.75/1.95          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.75/1.95            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.75/1.95              ( ( D ) = ( H ) ) ) ) ) )),
% 1.75/1.95    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 1.75/1.95  thf('0', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('1', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('2', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('3', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(d4_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.95     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.75/1.95       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.75/1.95  thf('4', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('5', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('6', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf(t134_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.75/1.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.95         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 1.75/1.95  thf('7', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X3) = (X6)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('8', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((X4) = (X0))
% 1.75/1.95          | ((X5) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['6', '7'])).
% 1.75/1.95  thf('9', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95          | ((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (sk_D)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['5', '8'])).
% 1.75/1.95  thf('10', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.75/1.95            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95          | ((X0) = (sk_D))
% 1.75/1.95          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['4', '9'])).
% 1.75/1.95  thf('11', plain,
% 1.75/1.95      ((((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (sk_D)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['10'])).
% 1.75/1.95  thf('12', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('13', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf(d3_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.75/1.95       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.75/1.95  thf('14', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('15', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 1.75/1.95           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.75/1.95      inference('sup+', [status(thm)], ['13', '14'])).
% 1.75/1.95  thf('16', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['12', '15'])).
% 1.75/1.95  thf('17', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 1.75/1.95           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.75/1.95      inference('sup+', [status(thm)], ['13', '14'])).
% 1.75/1.95  thf('18', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D @ X0)
% 1.75/1.95           = (k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0))),
% 1.75/1.95      inference('demod', [status(thm)], ['16', '17'])).
% 1.75/1.95  thf('19', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf(t113_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i]:
% 1.75/1.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.75/1.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.75/1.95  thf('20', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('21', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.75/1.95  thf('22', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.75/1.95              = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['18', '21'])).
% 1.75/1.95  thf('23', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('24', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('25', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0))
% 1.75/1.95          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.75/1.95  thf('26', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('27', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('28', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (sk_D))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['11', '27'])).
% 1.75/1.95  thf('29', plain,
% 1.75/1.95      (![X1 : $i, X2 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('30', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('31', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('32', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['30', '31'])).
% 1.75/1.95  thf('33', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('34', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.75/1.95  thf('35', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (sk_D))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['28', '34'])).
% 1.75/1.95  thf('36', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0)) | ((sk_H) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['35'])).
% 1.75/1.95  thf('37', plain, ((((sk_H) = (sk_D)) | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('condensation', [status(thm)], ['36'])).
% 1.75/1.95  thf('38', plain,
% 1.75/1.95      (![X1 : $i, X2 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('39', plain,
% 1.75/1.95      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['38'])).
% 1.75/1.95  thf('40', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('41', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['39', '40'])).
% 1.75/1.95  thf('42', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('43', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.95  thf('44', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ sk_H @ X0) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['37', '43'])).
% 1.75/1.95  thf('45', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('46', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (sk_D))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['44', '45'])).
% 1.75/1.95  thf('47', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['46'])).
% 1.75/1.95  thf('48', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('49', plain,
% 1.75/1.95      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95        | ((sk_H) = (sk_D)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['47', '48'])).
% 1.75/1.95  thf('50', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('51', plain, (((sk_H) = (sk_D))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 1.75/1.95  thf('52', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '51'])).
% 1.75/1.95  thf('53', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '51'])).
% 1.75/1.95  thf('54', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '51'])).
% 1.75/1.95  thf('55', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('56', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '51'])).
% 1.75/1.95  thf('57', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('58', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X4) = (X5)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('59', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k2_zfmisc_1 @ X5 @ X4))
% 1.75/1.95          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (X5))
% 1.75/1.95          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.75/1.95  thf('60', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k2_zfmisc_1 @ X1 @ X0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (X1)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['56', '59'])).
% 1.75/1.95  thf('61', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.75/1.95            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['55', '60'])).
% 1.75/1.95  thf('62', plain,
% 1.75/1.95      ((((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)
% 1.75/1.95            = (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['61'])).
% 1.75/1.95  thf('63', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('64', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('65', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X3) = (X6)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('66', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((X3) = (X0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((X3) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['64', '65'])).
% 1.75/1.95  thf('67', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 1.75/1.95          | ((X0) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (X3)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['63', '66'])).
% 1.75/1.95  thf('68', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (X0))
% 1.75/1.95          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['62', '67'])).
% 1.75/1.95  thf('69', plain,
% 1.75/1.95      ((((sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (sk_G))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['68'])).
% 1.75/1.95  thf('70', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.75/1.95  thf('71', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (sk_G))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['69', '70'])).
% 1.75/1.95  thf('72', plain,
% 1.75/1.95      ((((sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (sk_G))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['71'])).
% 1.75/1.95  thf('73', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('74', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('75', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.75/1.95      inference('sup+', [status(thm)], ['73', '74'])).
% 1.75/1.95  thf('76', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('77', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.75/1.95           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.75/1.95      inference('demod', [status(thm)], ['75', '76'])).
% 1.75/1.95  thf('78', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.75/1.95            = (k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (sk_G))
% 1.75/1.95          | ((sk_C) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['72', '77'])).
% 1.75/1.95  thf('79', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.75/1.95  thf('80', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (sk_G))
% 1.75/1.95          | ((sk_C) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['78', '79'])).
% 1.75/1.95  thf('81', plain,
% 1.75/1.95      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95        | ((sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (sk_G))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['54', '80'])).
% 1.75/1.95  thf('82', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('83', plain,
% 1.75/1.95      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (sk_G)) | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.75/1.95  thf('84', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('85', plain,
% 1.75/1.95      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['38'])).
% 1.75/1.95  thf('86', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['84', '85'])).
% 1.75/1.95  thf('87', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('88', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['86', '87'])).
% 1.75/1.95  thf('89', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('90', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['88', '89'])).
% 1.75/1.95  thf('91', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (sk_G)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['83', '90'])).
% 1.75/1.95  thf('92', plain,
% 1.75/1.95      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_C) = (sk_G))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['53', '91'])).
% 1.75/1.95  thf('93', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('94', plain, ((((sk_C) = (sk_G)) | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 1.75/1.95  thf('95', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.95  thf('96', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ sk_H @ X0) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['94', '95'])).
% 1.75/1.95  thf('97', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('98', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_C) = (sk_G))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['96', '97'])).
% 1.75/1.95  thf('99', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['98'])).
% 1.75/1.95  thf('100', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '51'])).
% 1.75/1.95  thf('101', plain,
% 1.75/1.95      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95        | ((sk_C) = (sk_G)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['99', '100'])).
% 1.75/1.95  thf('102', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('103', plain, (((sk_C) = (sk_G))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.75/1.95  thf('104', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['52', '103'])).
% 1.75/1.95  thf('105', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['52', '103'])).
% 1.75/1.95  thf('106', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['52', '103'])).
% 1.75/1.95  thf('107', plain,
% 1.75/1.95      ((((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)
% 1.75/1.95            = (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['61'])).
% 1.75/1.95  thf('108', plain, (((sk_C) = (sk_G))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.75/1.95  thf('109', plain, (((sk_C) = (sk_G))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.75/1.95  thf('110', plain,
% 1.75/1.95      ((((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G)
% 1.75/1.95            = (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))),
% 1.75/1.95      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.75/1.95  thf('111', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('112', plain,
% 1.75/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('113', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X4) = (X5)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('114', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k2_zfmisc_1 @ X4 @ X3))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (X4))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['112', '113'])).
% 1.75/1.95  thf('115', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((X3) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X5 @ X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X5 @ X4) = (k2_zfmisc_1 @ X2 @ X1)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['111', '114'])).
% 1.75/1.95  thf('116', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X2 @ X1))
% 1.75/1.95          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['110', '115'])).
% 1.75/1.95  thf('117', plain,
% 1.75/1.95      ((((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['116'])).
% 1.75/1.95  thf('118', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X4) = (X5)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('119', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (X1))
% 1.75/1.95          | ((sk_A) = (k1_xboole_0))
% 1.75/1.95          | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['117', '118'])).
% 1.75/1.95  thf('120', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['119'])).
% 1.75/1.95  thf('121', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('122', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['120', '121'])).
% 1.75/1.95  thf('123', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['122'])).
% 1.75/1.95  thf('124', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.75/1.95  thf('125', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['123', '124'])).
% 1.75/1.95  thf('126', plain,
% 1.75/1.95      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['125'])).
% 1.75/1.95  thf('127', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('128', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['126', '127'])).
% 1.75/1.95  thf('129', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['128'])).
% 1.75/1.95  thf('130', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.95  thf('131', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('132', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['130', '131'])).
% 1.75/1.95  thf('133', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('134', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['132', '133'])).
% 1.75/1.95  thf('135', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E))
% 1.75/1.95          | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['129', '134'])).
% 1.75/1.95  thf('136', plain,
% 1.75/1.95      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['106', '135'])).
% 1.75/1.95  thf('137', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('138', plain,
% 1.75/1.95      ((((sk_A) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 1.75/1.95  thf('139', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.75/1.95  thf('140', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 1.75/1.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 1.75/1.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.95  thf('141', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 1.75/1.95           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['139', '140'])).
% 1.75/1.95  thf('142', plain,
% 1.75/1.95      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.75/1.95      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.95  thf('143', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['141', '142'])).
% 1.75/1.95  thf('144', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ sk_A @ X2 @ X1 @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['138', '143'])).
% 1.75/1.95  thf('145', plain,
% 1.75/1.95      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_A) = (sk_E))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['105', '144'])).
% 1.75/1.95  thf('146', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('147', plain,
% 1.75/1.95      ((((sk_A) = (sk_E)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 1.75/1.95  thf('148', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.95  thf('149', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ sk_H @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['147', '148'])).
% 1.75/1.95  thf('150', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('151', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['149', '150'])).
% 1.75/1.95  thf('152', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['151'])).
% 1.75/1.95  thf('153', plain, ((((sk_A) = (sk_E)) | ((sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('condensation', [status(thm)], ['152'])).
% 1.75/1.95  thf('154', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['84', '85'])).
% 1.75/1.95  thf('155', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ X0 @ sk_G) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['153', '154'])).
% 1.75/1.95  thf('156', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('157', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['155', '156'])).
% 1.75/1.95  thf('158', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.75/1.95  thf('159', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_A) = (sk_E))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['157', '158'])).
% 1.75/1.95  thf('160', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['159'])).
% 1.75/1.95  thf('161', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['52', '103'])).
% 1.75/1.95  thf('162', plain,
% 1.75/1.95      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.75/1.95        | ((sk_A) = (sk_E)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['160', '161'])).
% 1.75/1.95  thf('163', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('164', plain, (((sk_A) = (sk_E))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.75/1.95  thf('165', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_B @ sk_G @ sk_H)
% 1.75/1.95         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.75/1.95      inference('demod', [status(thm)], ['104', '164'])).
% 1.75/1.95  thf('166', plain,
% 1.75/1.95      ((((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['116'])).
% 1.75/1.95  thf('167', plain, (((sk_A) = (sk_E))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.75/1.95  thf('168', plain, (((sk_A) = (sk_E))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.75/1.95  thf('169', plain, (((sk_A) = (sk_E))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.75/1.95  thf('170', plain,
% 1.75/1.95      ((((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 1.75/1.95  thf('171', plain,
% 1.75/1.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.95         (((X3) = (k1_xboole_0))
% 1.75/1.95          | ((X4) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 1.75/1.95          | ((X3) = (X6)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 1.75/1.95  thf('172', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 1.75/1.95          | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_B) = (X0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0))
% 1.75/1.95          | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['170', '171'])).
% 1.75/1.95  thf('173', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (sk_F))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('eq_res', [status(thm)], ['172'])).
% 1.75/1.95  thf('174', plain,
% 1.75/1.95      ((((sk_A) != (sk_E))
% 1.75/1.95        | ((sk_B) != (sk_F))
% 1.75/1.95        | ((sk_C) != (sk_G))
% 1.75/1.95        | ((sk_D) != (sk_H)))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf('175', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.75/1.95      inference('split', [status(esa)], ['174'])).
% 1.75/1.95  thf('176', plain, (((sk_H) = (sk_D))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 1.75/1.95  thf('177', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.75/1.95      inference('split', [status(esa)], ['174'])).
% 1.75/1.95  thf('178', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.75/1.95      inference('sup-', [status(thm)], ['176', '177'])).
% 1.75/1.95  thf('179', plain, ((((sk_D) = (sk_H)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['178'])).
% 1.75/1.95  thf('180', plain, (((sk_C) = (sk_G))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.75/1.95  thf('181', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.75/1.95      inference('split', [status(esa)], ['174'])).
% 1.75/1.95  thf('182', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.75/1.95      inference('sup-', [status(thm)], ['180', '181'])).
% 1.75/1.95  thf('183', plain, ((((sk_C) = (sk_G)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['182'])).
% 1.75/1.95  thf('184', plain, (((sk_A) = (sk_E))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.75/1.95  thf('185', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.75/1.95      inference('split', [status(esa)], ['174'])).
% 1.75/1.95  thf('186', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.75/1.95      inference('sup-', [status(thm)], ['184', '185'])).
% 1.75/1.95  thf('187', plain, ((((sk_A) = (sk_E)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['186'])).
% 1.75/1.95  thf('188', plain,
% 1.75/1.95      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 1.75/1.95       ~ (((sk_D) = (sk_H)))),
% 1.75/1.95      inference('split', [status(esa)], ['174'])).
% 1.75/1.95  thf('189', plain, (~ (((sk_B) = (sk_F)))),
% 1.75/1.95      inference('sat_resolution*', [status(thm)], ['179', '183', '187', '188'])).
% 1.75/1.95  thf('190', plain, (((sk_B) != (sk_F))),
% 1.75/1.95      inference('simpl_trail', [status(thm)], ['175', '189'])).
% 1.75/1.95  thf('191', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['173', '190'])).
% 1.75/1.95  thf('192', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('193', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['191', '192'])).
% 1.75/1.95  thf('194', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((k3_zfmisc_1 @ sk_E @ sk_B @ sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['193'])).
% 1.75/1.95  thf('195', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.75/1.95  thf('196', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['194', '195'])).
% 1.75/1.95  thf('197', plain,
% 1.75/1.95      ((((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['196'])).
% 1.75/1.95  thf('198', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((X1) = (k1_xboole_0))
% 1.75/1.95          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.75/1.95  thf('199', plain,
% 1.75/1.95      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['197', '198'])).
% 1.75/1.95  thf('200', plain,
% 1.75/1.95      ((((sk_B) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['199'])).
% 1.75/1.95  thf('201', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['132', '133'])).
% 1.75/1.95  thf('202', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         (((k4_zfmisc_1 @ X2 @ sk_B @ X1 @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_H) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['200', '201'])).
% 1.75/1.95  thf('203', plain,
% 1.75/1.95      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.75/1.95        | ((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['165', '202'])).
% 1.75/1.95  thf('204', plain,
% 1.75/1.95      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.75/1.95  thf('205', plain,
% 1.75/1.95      ((((sk_E) = (k1_xboole_0))
% 1.75/1.95        | ((sk_G) = (k1_xboole_0))
% 1.75/1.95        | ((sk_H) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['203', '204'])).
% 1.75/1.95  thf('206', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.95  thf('207', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ sk_H @ X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['205', '206'])).
% 1.75/1.95  thf('208', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('209', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['207', '208'])).
% 1.75/1.95  thf('210', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((X0) = (k1_xboole_0))
% 1.75/1.95          | ((sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['209'])).
% 1.75/1.95  thf('211', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)))),
% 1.75/1.95      inference('condensation', [status(thm)], ['210'])).
% 1.75/1.95  thf('212', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.75/1.95      inference('sup+', [status(thm)], ['84', '85'])).
% 1.75/1.95  thf('213', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ X1 @ X0 @ sk_G) = (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['211', '212'])).
% 1.75/1.95  thf('214', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) @ sk_H @ X0)
% 1.75/1.95            != (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 1.75/1.95  thf('215', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k3_zfmisc_1 @ k1_xboole_0 @ sk_H @ X0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['213', '214'])).
% 1.75/1.95  thf('216', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.75/1.95  thf('217', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.95          | ((sk_E) = (k1_xboole_0))
% 1.75/1.95          | ((X0) = (k1_xboole_0)))),
% 1.75/1.95      inference('demod', [status(thm)], ['215', '216'])).
% 1.75/1.95  thf('218', plain,
% 1.75/1.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 1.75/1.95      inference('simplify', [status(thm)], ['217'])).
% 1.75/1.95  thf('219', plain, (((sk_E) = (k1_xboole_0))),
% 1.75/1.95      inference('condensation', [status(thm)], ['218'])).
% 1.75/1.95  thf('220', plain, (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (sk_E))),
% 1.75/1.95      inference('demod', [status(thm)], ['2', '219'])).
% 1.75/1.95  thf('221', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 1.75/1.95      inference('demod', [status(thm)], ['141', '142'])).
% 1.75/1.95  thf('222', plain, (((sk_E) = (k1_xboole_0))),
% 1.75/1.95      inference('condensation', [status(thm)], ['218'])).
% 1.75/1.95  thf('223', plain, (((sk_E) = (k1_xboole_0))),
% 1.75/1.95      inference('condensation', [status(thm)], ['218'])).
% 1.75/1.95  thf('224', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.95         ((k4_zfmisc_1 @ sk_E @ X2 @ X1 @ X0) = (sk_E))),
% 1.75/1.95      inference('demod', [status(thm)], ['221', '222', '223'])).
% 1.75/1.95  thf('225', plain, (((sk_E) != (sk_E))),
% 1.75/1.95      inference('demod', [status(thm)], ['220', '224'])).
% 1.75/1.95  thf('226', plain, ($false), inference('simplify', [status(thm)], ['225'])).
% 1.75/1.95  
% 1.75/1.95  % SZS output end Refutation
% 1.75/1.95  
% 1.75/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
