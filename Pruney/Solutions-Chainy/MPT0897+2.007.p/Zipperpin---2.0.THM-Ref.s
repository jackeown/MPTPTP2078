%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s5bkjFK0WG

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:41 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  113 (1873 expanded)
%              Number of leaves         :   17 ( 568 expanded)
%              Depth                    :   38
%              Number of atoms          : 1176 (27722 expanded)
%              Number of equality atoms :  183 (3958 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('10',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('20',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('22',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X5 = X1 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['21','35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(eq_res,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('61',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['58'])).

thf('62',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['34'])).

thf('65',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['58'])).

thf('66',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(eq_res,[status(thm)],['72'])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(demod,[status(thm)],['75','77'])).

thf('79',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['58'])).

thf('83',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['58'])).

thf('86',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['63','67','84','85'])).

thf('87',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['59','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['57','87'])).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['2','92'])).

thf('94',plain,(
    $false ),
    inference(simplify,[status(thm)],['93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s5bkjFK0WG
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 292 iterations in 0.160s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.43/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(sk_H_type, type, sk_H: $i).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.43/0.62  thf(t57_mcart_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.43/0.62     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.43/0.62       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.43/0.62           ( ( D ) = ( H ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.43/0.62        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.43/0.62          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.43/0.62              ( ( D ) = ( H ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf(d3_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.43/0.62       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf(d4_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.43/0.62       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.43/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(t37_mcart_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.62     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.43/0.62       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ((X12) = (X15)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((X4) = (X0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.43/0.62            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.43/0.62          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((X0) = (sk_D)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.43/0.62          | ((X0) = (sk_D))
% 0.43/0.62          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.43/0.62          | ((X0) = (sk_D))
% 0.43/0.62          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.43/0.62        | ((sk_H) = (sk_D)))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('20', plain, (((sk_H) = (sk_D))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('demod', [status(thm)], ['8', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('demod', [status(thm)], ['8', '20'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ((X11) = (X14)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((X5) = (X1))
% 0.43/0.62          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.43/0.62          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((X1) = (X5)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['23', '26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.43/0.62          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((X1) = (X5)))),
% 0.43/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((sk_C) = (X1))
% 0.43/0.62          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('demod', [status(thm)], ['8', '20'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((sk_C) = (X1))
% 0.43/0.62          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((sk_C) = (X1)))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain, (((sk_C) = (sk_G))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ((X10) = (X13)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.43/0.62          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.43/0.62          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.43/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.43/0.62          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.43/0.62          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H) = (k1_xboole_0))
% 0.43/0.62          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['36', '41'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 0.43/0.62         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '35'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.43/0.62          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.43/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.43/0.62            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ((X10) = (X13)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.43/0.62          | ((sk_A) = (X3))
% 0.43/0.62          | ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.43/0.62          | ((sk_A) = (X3))
% 0.43/0.62          | ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((sk_A) = (sk_E)))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      ((((sk_A) != (sk_E))
% 0.43/0.62        | ((sk_B) != (sk_F))
% 0.43/0.62        | ((sk_C) != (sk_G))
% 0.43/0.62        | ((sk_D) != (sk_H)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('59', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.43/0.62      inference('split', [status(esa)], ['58'])).
% 0.43/0.62  thf('60', plain, (((sk_H) = (sk_D))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('61', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.43/0.62      inference('split', [status(esa)], ['58'])).
% 0.43/0.62  thf('62', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.62  thf('63', plain, ((((sk_D) = (sk_H)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['62'])).
% 0.43/0.62  thf('64', plain, (((sk_C) = (sk_G))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['34'])).
% 0.43/0.62  thf('65', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.43/0.62      inference('split', [status(esa)], ['58'])).
% 0.43/0.62  thf('66', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.62  thf('67', plain, ((((sk_C) = (sk_G)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['66'])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.43/0.62          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ((X11) = (X14)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.43/0.62          | ((sk_B) = (X2))
% 0.43/0.62          | ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.43/0.62          | ((sk_B) = (X2))
% 0.43/0.62          | ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['70', '71'])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((sk_B) = (sk_F)))),
% 0.43/0.62      inference('eq_res', [status(thm)], ['72'])).
% 0.43/0.62  thf('74', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.43/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 0.43/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.43/0.62          | ((sk_B) = (sk_F)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['73', '74'])).
% 0.43/0.62  thf(t113_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i]:
% 0.43/0.62         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.62  thf('77', plain,
% 0.43/0.62      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['76'])).
% 0.43/0.62  thf('78', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((sk_B) = (sk_F)))),
% 0.43/0.62      inference('demod', [status(thm)], ['75', '77'])).
% 0.43/0.62  thf('79', plain,
% 0.43/0.62      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('80', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['78', '79'])).
% 0.43/0.62  thf('81', plain, (((sk_B) = (sk_F))),
% 0.43/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.43/0.62  thf('82', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.43/0.62      inference('split', [status(esa)], ['58'])).
% 0.43/0.62  thf('83', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.43/0.62  thf('84', plain, ((((sk_B) = (sk_F)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['83'])).
% 0.43/0.62  thf('85', plain,
% 0.43/0.62      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.43/0.62       ~ (((sk_D) = (sk_H)))),
% 0.43/0.62      inference('split', [status(esa)], ['58'])).
% 0.43/0.62  thf('86', plain, (~ (((sk_A) = (sk_E)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['63', '67', '84', '85'])).
% 0.43/0.62  thf('87', plain, (((sk_A) != (sk_E))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['59', '86'])).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      (![X0 : $i]: ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['57', '87'])).
% 0.43/0.62  thf('89', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.43/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.43/0.62  thf('90', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 0.43/0.62           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['88', '89'])).
% 0.43/0.62  thf('91', plain,
% 0.43/0.62      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['76'])).
% 0.43/0.62  thf('92', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['90', '91'])).
% 0.43/0.62  thf('93', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['2', '92'])).
% 0.43/0.62  thf('94', plain, ($false), inference('simplify', [status(thm)], ['93'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
