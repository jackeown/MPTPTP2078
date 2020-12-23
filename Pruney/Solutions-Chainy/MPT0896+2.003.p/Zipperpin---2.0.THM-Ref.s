%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WHDKzr0QPn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:39 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 920 expanded)
%              Number of leaves         :   18 ( 265 expanded)
%              Depth                    :   34
%              Number of atoms          : 1670 (17296 expanded)
%              Number of equality atoms :  367 (3977 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
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

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = X4 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = X0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = X3 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['26'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','40'])).

thf('42',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('50',plain,(
    sk_G != k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','50'])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( sk_A = sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_E ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference(demod,[status(thm)],['56','69'])).

thf('71',plain,
    ( ( sk_B = sk_F )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_B )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('75',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['80'])).

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf('87',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('108',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('109',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf('112',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['95','96','97'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('116',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['72'])).

thf('122',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('125',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['72'])).

thf('126',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['66','67','68'])).

thf('129',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['72'])).

thf('130',plain,
    ( ( sk_E != sk_E )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['72'])).

thf('133',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['123','127','131','132'])).

thf('134',plain,(
    sk_B != sk_F ),
    inference(simpl_trail,[status(thm)],['73','133'])).

thf('135',plain,
    ( ( k2_zfmisc_1 @ sk_E @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['71','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('137',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    sk_A = sk_E ),
    inference('simplify_reflect-',[status(thm)],['66','67','68'])).

thf('141',plain,(
    sk_E != k1_xboole_0 ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WHDKzr0QPn
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 584 iterations in 0.200s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(sk_H_type, type, sk_H: $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.65  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.47/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(d4_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.47/0.65       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf(t56_mcart_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.47/0.65     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.47/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.65         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.47/0.65         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.47/0.65           ( ( D ) = ( H ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.47/0.65        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.47/0.65          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.65            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.47/0.65            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.47/0.65              ( ( D ) = ( H ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.65         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf(t134_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.47/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.65         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X4) = (X5)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k2_zfmisc_1 @ X5 @ X4))
% 0.47/0.65          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (X5))
% 0.47/0.65          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((sk_D) = (k1_xboole_0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '4'])).
% 0.47/0.65  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (X1)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.47/0.65            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '7'])).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)
% 0.47/0.65            = (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['8'])).
% 0.47/0.65  thf(d3_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.47/0.65       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X4) = (X5)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k2_zfmisc_1 @ X4 @ X3))
% 0.47/0.65          | ((k2_zfmisc_1 @ X2 @ X1) = (X4))
% 0.47/0.65          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((X3) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X5 @ X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X5 @ X4) = (k2_zfmisc_1 @ X2 @ X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['10', '13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X2 @ X1))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '14'])).
% 0.47/0.65  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X2 @ X1))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)
% 0.47/0.65            = (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['8'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X3) = (X6)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((X3) = (X0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((X3) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 0.47/0.65          | ((X0) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (X3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['19', '22'])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '23'])).
% 0.47/0.65  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.47/0.65          | ((sk_C) = (X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (sk_G))
% 0.47/0.65        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['26'])).
% 0.47/0.65  thf(t35_mcart_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.65         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.47/0.65       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.47/0.65          | ((X16) = (k1_xboole_0))
% 0.47/0.65          | ((X15) = (k1_xboole_0))
% 0.47/0.65          | ((X14) = (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (sk_G))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      ((((sk_C) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (sk_G)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.65  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 0.47/0.65  thf(t113_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (sk_G))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.65  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('40', plain, (((sk_C) = (sk_G))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X2 @ X1))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['17', '40'])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.47/0.65        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['41'])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.47/0.65          | ((X16) = (k1_xboole_0))
% 0.47/0.65          | ((X15) = (k1_xboole_0))
% 0.47/0.65          | ((X14) = (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_G) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      ((((sk_G) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.65  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('49', plain, (((sk_C) = (sk_G))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.47/0.65  thf('50', plain, (((sk_G) != (k1_xboole_0))),
% 0.47/0.65      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '50'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X3) = (X6)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (X0))
% 0.47/0.65          | ((sk_A) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.65  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (X0)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['53', '54', '55'])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '50'])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X4) = (X5)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_A) = (X1))
% 0.47/0.65          | ((sk_A) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.65  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_A) = (X1)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      ((((sk_A) = (sk_E)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['62'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (sk_E))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.65  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('69', plain, (((sk_A) = (sk_E))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['66', '67', '68'])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ sk_E @ sk_F) != (k2_zfmisc_1 @ X1 @ X0))
% 0.47/0.65          | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 0.47/0.65          | ((sk_B) = (X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['56', '69'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((((sk_B) = (sk_F)) | ((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['70'])).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      ((((sk_A) != (sk_E))
% 0.47/0.65        | ((sk_B) != (sk_F))
% 0.47/0.65        | ((sk_C) != (sk_G))
% 0.47/0.65        | ((sk_D) != (sk_H)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('73', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.47/0.65      inference('split', [status(esa)], ['72'])).
% 0.47/0.65  thf('74', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.65         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (((X3) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.47/0.65          | ((X3) = (X6)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.65          | ((X4) = (X0))
% 0.47/0.65          | ((X5) = (k1_xboole_0))
% 0.47/0.65          | ((X4) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.47/0.65          | ((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (sk_D)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['75', '78'])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.47/0.65            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.47/0.65          | ((X0) = (sk_D))
% 0.47/0.65          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['74', '79'])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      ((((sk_H) = (k1_xboole_0))
% 0.47/0.65        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['80'])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf('83', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 0.47/0.65            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ((sk_H) = (sk_D))
% 0.47/0.65          | ((sk_H) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['81', '82'])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (![X1 : $i, X2 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0))
% 0.47/0.65          | ((sk_H) = (k1_xboole_0))
% 0.47/0.65          | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['83', '85'])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.47/0.65         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.47/0.65           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.47/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf('92', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.47/0.65           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.47/0.65      inference('demod', [status(thm)], ['90', '91'])).
% 0.47/0.65  thf('93', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.47/0.65          | ((X16) = (k1_xboole_0))
% 0.47/0.65          | ((X15) = (k1_xboole_0))
% 0.47/0.65          | ((X14) = (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.47/0.65  thf('94', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.47/0.65        | ((sk_D) = (k1_xboole_0))
% 0.47/0.65        | ((sk_C) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['87', '94'])).
% 0.47/0.65  thf('96', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('97', plain, (((sk_D) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('98', plain,
% 0.47/0.65      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('99', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D))
% 0.47/0.65        | ((sk_H) = (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['86', '98'])).
% 0.47/0.65  thf('100', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['99'])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D))
% 0.47/0.65        | ((sk_H) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.65  thf('103', plain,
% 0.47/0.65      ((((sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['102'])).
% 0.47/0.65  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('105', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('106', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['103', '104', '105'])).
% 0.47/0.65  thf('107', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.65           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.47/0.65  thf('108', plain,
% 0.47/0.65      (![X1 : $i, X2 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('109', plain,
% 0.47/0.65      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['108'])).
% 0.47/0.65  thf('110', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['107', '109'])).
% 0.47/0.65  thf('111', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.47/0.65          | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['106', '110'])).
% 0.47/0.65  thf('112', plain,
% 0.47/0.65      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('113', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D))
% 0.47/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['111', '112'])).
% 0.47/0.65  thf('114', plain,
% 0.47/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['113'])).
% 0.47/0.65  thf('115', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('116', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_H) = (sk_D))
% 0.47/0.65        | ((sk_A) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.47/0.65  thf('117', plain,
% 0.47/0.65      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.65  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('119', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('120', plain, (((sk_H) = (sk_D))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['117', '118', '119'])).
% 0.47/0.65  thf('121', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.47/0.65      inference('split', [status(esa)], ['72'])).
% 0.47/0.65  thf('122', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['120', '121'])).
% 0.47/0.65  thf('123', plain, ((((sk_D) = (sk_H)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.65  thf('124', plain, (((sk_C) = (sk_G))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.47/0.65  thf('125', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.47/0.65      inference('split', [status(esa)], ['72'])).
% 0.47/0.65  thf('126', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['124', '125'])).
% 0.47/0.65  thf('127', plain, ((((sk_C) = (sk_G)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['126'])).
% 0.47/0.65  thf('128', plain, (((sk_A) = (sk_E))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['66', '67', '68'])).
% 0.47/0.65  thf('129', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.47/0.65      inference('split', [status(esa)], ['72'])).
% 0.47/0.65  thf('130', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['128', '129'])).
% 0.47/0.65  thf('131', plain, ((((sk_A) = (sk_E)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['130'])).
% 0.47/0.65  thf('132', plain,
% 0.47/0.65      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.47/0.65       ~ (((sk_D) = (sk_H)))),
% 0.47/0.65      inference('split', [status(esa)], ['72'])).
% 0.47/0.65  thf('133', plain, (~ (((sk_B) = (sk_F)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['123', '127', '131', '132'])).
% 0.47/0.65  thf('134', plain, (((sk_B) != (sk_F))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['73', '133'])).
% 0.47/0.65  thf('135', plain, (((k2_zfmisc_1 @ sk_E @ sk_B) = (k1_xboole_0))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['71', '134'])).
% 0.47/0.65  thf('136', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X0) = (k1_xboole_0))
% 0.47/0.65          | ((X1) = (k1_xboole_0))
% 0.47/0.65          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('137', plain,
% 0.47/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.65        | ((sk_E) = (k1_xboole_0))
% 0.47/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['135', '136'])).
% 0.47/0.65  thf('138', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['137'])).
% 0.47/0.65  thf('139', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('140', plain, (((sk_A) = (sk_E))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['66', '67', '68'])).
% 0.47/0.65  thf('141', plain, (((sk_E) != (k1_xboole_0))),
% 0.47/0.65      inference('demod', [status(thm)], ['139', '140'])).
% 0.47/0.65  thf('142', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('143', plain, ($false),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['138', '141', '142'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
