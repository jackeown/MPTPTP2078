%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSzhL08wIp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:39 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 677 expanded)
%              Number of leaves         :   18 ( 204 expanded)
%              Depth                    :   34
%              Number of atoms          : 1471 (11697 expanded)
%              Number of equality atoms :  317 (2614 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X12 @ X11 @ X10 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(eq_res,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X12 @ X11 @ X10 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X12 @ X11 @ X10 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(condensation,[status(thm)],['30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X12 @ X11 @ X10 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X10 = X15 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(demod,[status(thm)],['53','59','60'])).

thf('62',plain,
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

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('64',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('73',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('75',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67','68'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['77','79'])).

thf('81',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67','68'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['40'])).

thf('85',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['82'])).

thf('89',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X12 @ X11 @ X10 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X5 = X1 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['82'])).

thf('98',plain,(
    sk_H != k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','98','99'])).

thf('101',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(eq_res,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['40'])).

thf('109',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('112',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['40'])).

thf('113',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['40'])).

thf('116',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['86','110','114','115'])).

thf('117',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['41','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','117'])).

thf('119',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_F )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('126',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['122','123','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSzhL08wIp
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:29:05 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 772 iterations in 0.250s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.54/0.71  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.54/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.71  thf(sk_G_type, type, sk_G: $i).
% 0.54/0.71  thf(sk_H_type, type, sk_H: $i).
% 0.54/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.54/0.71  thf(d3_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.54/0.71       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.71           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.54/0.71      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf(d4_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.54/0.71       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.71         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.54/0.71           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.54/0.71      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.71           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.71  thf(t56_mcart_1, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.54/0.71     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.54/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.54/0.71           ( ( D ) = ( H ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.54/0.71        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.54/0.71          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.54/0.71              ( ( D ) = ( H ) ) ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.54/0.71         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.71           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.71  thf(t36_mcart_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.71     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.54/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.54/0.71         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.71         (((X10) = (k1_xboole_0))
% 0.54/0.71          | ((X11) = (k1_xboole_0))
% 0.54/0.71          | ((X12) = (k1_xboole_0))
% 0.54/0.71          | ((k3_zfmisc_1 @ X12 @ X11 @ X10) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.54/0.71          | ((X12) = (X13)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.71         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.54/0.71          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.54/0.71          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.54/0.71          | ((X1) = (k1_xboole_0))
% 0.54/0.71          | ((X0) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.54/0.71            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.54/0.71          | ((sk_D) = (k1_xboole_0))
% 0.54/0.71          | ((sk_C) = (k1_xboole_0))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['5', '8'])).
% 0.54/0.71  thf('10', plain, (((sk_C) != (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('11', plain, (((sk_D) != (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('12', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.54/0.71            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.54/0.71      inference('simplify_reflect-', [status(thm)], ['9', '10', '11'])).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.71         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.54/0.71            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2))
% 0.54/0.71          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['4', '12'])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.71        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.54/0.71      inference('eq_res', [status(thm)], ['13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.54/0.71            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.72  thf('18', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.72         (((X10) = (k1_xboole_0))
% 0.54/0.72          | ((X11) = (k1_xboole_0))
% 0.54/0.72          | ((X12) = (k1_xboole_0))
% 0.54/0.72          | ((k3_zfmisc_1 @ X12 @ X11 @ X10) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.54/0.72          | ((X12) = (X13)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.54/0.72  thf('20', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((sk_A) = (X3))
% 0.54/0.72          | ((sk_A) = (k1_xboole_0))
% 0.54/0.72          | ((sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.72  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('23', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((sk_A) = (X3))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['20', '21', '22'])).
% 0.54/0.72  thf('24', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.72  thf('25', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.72         (((X10) = (k1_xboole_0))
% 0.54/0.72          | ((X11) = (k1_xboole_0))
% 0.54/0.72          | ((X12) = (k1_xboole_0))
% 0.54/0.72          | ((k3_zfmisc_1 @ X12 @ X11 @ X10) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.54/0.72          | ((X11) = (X14)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.54/0.72  thf('26', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((sk_B) = (X2))
% 0.54/0.72          | ((sk_A) = (k1_xboole_0))
% 0.54/0.72          | ((sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('29', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((sk_B) = (X2))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['26', '27', '28'])).
% 0.54/0.72  thf('30', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((sk_B) = (sk_F))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('eq_res', [status(thm)], ['29'])).
% 0.54/0.72  thf('31', plain,
% 0.54/0.72      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.54/0.72      inference('condensation', [status(thm)], ['30'])).
% 0.54/0.72  thf(t113_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((sk_B) = (sk_F))
% 0.54/0.72        | ((sk_A) = (k1_xboole_0))
% 0.54/0.72        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.72  thf('34', plain,
% 0.54/0.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['33'])).
% 0.54/0.72  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('37', plain, (((sk_B) = (sk_F))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0))
% 0.54/0.72          | ((sk_A) = (X3))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['23', '37'])).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((sk_A) = (sk_E))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0)))),
% 0.54/0.72      inference('eq_res', [status(thm)], ['38'])).
% 0.54/0.72  thf('40', plain,
% 0.54/0.72      ((((sk_A) != (sk_E))
% 0.54/0.72        | ((sk_B) != (sk_F))
% 0.54/0.72        | ((sk_C) != (sk_G))
% 0.54/0.72        | ((sk_D) != (sk_H)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('41', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.54/0.72      inference('split', [status(esa)], ['40'])).
% 0.54/0.72  thf('42', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.72           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.54/0.72         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.72           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.72         (((X10) = (k1_xboole_0))
% 0.54/0.72          | ((X11) = (k1_xboole_0))
% 0.54/0.72          | ((X12) = (k1_xboole_0))
% 0.54/0.72          | ((k3_zfmisc_1 @ X12 @ X11 @ X10) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.54/0.72          | ((X10) = (X15)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.72          | ((X4) = (X0))
% 0.54/0.72          | ((X6) = (k1_xboole_0))
% 0.54/0.72          | ((X5) = (k1_xboole_0))
% 0.54/0.72          | ((X4) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.72  thf('47', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.54/0.72            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.54/0.72          | ((X0) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((X2) = (k1_xboole_0))
% 0.54/0.72          | ((X0) = (sk_D)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['43', '46'])).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.54/0.72            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.54/0.72          | ((X0) = (sk_D))
% 0.54/0.72          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['42', '47'])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      ((((sk_H) = (k1_xboole_0))
% 0.54/0.72        | ((sk_G) = (k1_xboole_0))
% 0.54/0.72        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 0.54/0.72        | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('eq_res', [status(thm)], ['48'])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.72  thf('51', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.54/0.72          | ((sk_H) = (sk_D))
% 0.54/0.72          | ((sk_G) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['49', '50'])).
% 0.54/0.72  thf('52', plain,
% 0.54/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1)
% 0.54/0.72            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ X0) @ X1))
% 0.54/0.72          | ((sk_H) = (k1_xboole_0))
% 0.54/0.72          | ((sk_G) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['51', '52'])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (![X1 : $i, X2 : $i]:
% 0.54/0.72         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.72  thf('55', plain,
% 0.54/0.72      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.54/0.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.54/0.72  thf('57', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.54/0.72           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['55', '56'])).
% 0.54/0.72  thf('58', plain,
% 0.54/0.72      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.54/0.72  thf('59', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['57', '58'])).
% 0.54/0.72  thf('60', plain,
% 0.54/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.72         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.54/0.72           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.54/0.72      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.54/0.72  thf('61', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1))
% 0.54/0.72          | ((sk_H) = (k1_xboole_0))
% 0.54/0.72          | ((sk_G) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('demod', [status(thm)], ['53', '59', '60'])).
% 0.54/0.72  thf('62', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.54/0.72         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(t55_mcart_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.72     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.54/0.72         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.54/0.72       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.54/0.72  thf('63', plain,
% 0.54/0.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19) != (k1_xboole_0))
% 0.54/0.72          | ((X19) = (k1_xboole_0))
% 0.54/0.72          | ((X18) = (k1_xboole_0))
% 0.54/0.72          | ((X17) = (k1_xboole_0))
% 0.54/0.72          | ((X16) = (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.54/0.72  thf('64', plain,
% 0.54/0.72      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.54/0.72        | ((sk_A) = (k1_xboole_0))
% 0.54/0.72        | ((sk_B) = (k1_xboole_0))
% 0.54/0.72        | ((sk_C) = (k1_xboole_0))
% 0.54/0.72        | ((sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.72  thf('65', plain, (((sk_D) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('66', plain, (((sk_C) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('69', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)],
% 0.54/0.72                ['64', '65', '66', '67', '68'])).
% 0.54/0.72  thf('70', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((sk_H) = (sk_D))
% 0.54/0.72        | ((sk_G) = (k1_xboole_0))
% 0.54/0.72        | ((sk_H) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['61', '69'])).
% 0.54/0.72  thf('71', plain,
% 0.54/0.72      ((((sk_H) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['70'])).
% 0.54/0.72  thf('72', plain,
% 0.54/0.72      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.54/0.72         (((X20) != (k1_xboole_0))
% 0.54/0.72          | ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20) = (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.54/0.72  thf('73', plain,
% 0.54/0.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.72         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['72'])).
% 0.54/0.72  thf('74', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (sk_D))
% 0.54/0.72          | ((sk_G) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['71', '73'])).
% 0.54/0.72  thf('75', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)],
% 0.54/0.72                ['64', '65', '66', '67', '68'])).
% 0.54/0.72  thf('76', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((sk_G) = (k1_xboole_0))
% 0.54/0.72        | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.72  thf('77', plain, ((((sk_H) = (sk_D)) | ((sk_G) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['76'])).
% 0.54/0.72  thf('78', plain,
% 0.54/0.72      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.54/0.72         (((X18) != (k1_xboole_0))
% 0.54/0.72          | ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20) = (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.54/0.72  thf('79', plain,
% 0.54/0.72      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.54/0.72         ((k4_zfmisc_1 @ X16 @ X17 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['78'])).
% 0.54/0.72  thf('80', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['77', '79'])).
% 0.54/0.72  thf('81', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)],
% 0.54/0.72                ['64', '65', '66', '67', '68'])).
% 0.54/0.72  thf('82', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.54/0.72  thf('83', plain, (((sk_H) = (sk_D))),
% 0.54/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.54/0.72  thf('84', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.54/0.72      inference('split', [status(esa)], ['40'])).
% 0.54/0.72  thf('85', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.72  thf('86', plain, ((((sk_D) = (sk_H)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.72  thf('87', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.54/0.72         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('88', plain, (((sk_H) = (sk_D))),
% 0.54/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.54/0.72  thf('89', plain,
% 0.54/0.72      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.54/0.72         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.54/0.72      inference('demod', [status(thm)], ['87', '88'])).
% 0.54/0.72  thf('90', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.72           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.72  thf('91', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.54/0.72           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.72  thf('92', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.72         (((X10) = (k1_xboole_0))
% 0.54/0.72          | ((X11) = (k1_xboole_0))
% 0.54/0.72          | ((X12) = (k1_xboole_0))
% 0.54/0.72          | ((k3_zfmisc_1 @ X12 @ X11 @ X10) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.54/0.72          | ((X11) = (X14)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.54/0.72  thf('93', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.72         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.72          | ((X5) = (X1))
% 0.54/0.72          | ((X6) = (k1_xboole_0))
% 0.54/0.72          | ((X5) = (k1_xboole_0))
% 0.54/0.72          | ((X4) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['91', '92'])).
% 0.54/0.72  thf('94', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.54/0.72            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.54/0.72          | ((X0) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (X5)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['90', '93'])).
% 0.54/0.72  thf('95', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.54/0.72            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.72          | ((sk_C) = (X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.54/0.72          | ((sk_C) = (k1_xboole_0))
% 0.54/0.72          | ((sk_H) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['89', '94'])).
% 0.54/0.72  thf('96', plain, (((sk_D) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('97', plain, (((sk_H) = (sk_D))),
% 0.54/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.54/0.72  thf('98', plain, (((sk_H) != (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['96', '97'])).
% 0.54/0.72  thf('99', plain, (((sk_C) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('100', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.72         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.54/0.72            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.72          | ((sk_C) = (X1))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['95', '98', '99'])).
% 0.54/0.72  thf('101', plain,
% 0.54/0.72      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.54/0.72      inference('eq_res', [status(thm)], ['100'])).
% 0.54/0.72  thf('102', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.72  thf('103', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((sk_C) = (sk_G))
% 0.54/0.72        | ((sk_A) = (k1_xboole_0))
% 0.54/0.72        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['101', '102'])).
% 0.54/0.72  thf('104', plain,
% 0.54/0.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['103'])).
% 0.54/0.72  thf('105', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('107', plain, (((sk_C) = (sk_G))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['104', '105', '106'])).
% 0.54/0.72  thf('108', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.54/0.72      inference('split', [status(esa)], ['40'])).
% 0.54/0.72  thf('109', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['107', '108'])).
% 0.54/0.72  thf('110', plain, ((((sk_C) = (sk_G)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['109'])).
% 0.54/0.72  thf('111', plain, (((sk_B) = (sk_F))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.54/0.72  thf('112', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.54/0.72      inference('split', [status(esa)], ['40'])).
% 0.54/0.72  thf('113', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['111', '112'])).
% 0.54/0.72  thf('114', plain, ((((sk_B) = (sk_F)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['113'])).
% 0.54/0.72  thf('115', plain,
% 0.54/0.72      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.54/0.72       ~ (((sk_D) = (sk_H)))),
% 0.54/0.72      inference('split', [status(esa)], ['40'])).
% 0.54/0.72  thf('116', plain, (~ (((sk_A) = (sk_E)))),
% 0.54/0.72      inference('sat_resolution*', [status(thm)], ['86', '110', '114', '115'])).
% 0.54/0.72  thf('117', plain, (((sk_A) != (sk_E))),
% 0.54/0.72      inference('simpl_trail', [status(thm)], ['41', '116'])).
% 0.54/0.72  thf('118', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['39', '117'])).
% 0.54/0.72  thf('119', plain, (((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0))),
% 0.54/0.72      inference('condensation', [status(thm)], ['118'])).
% 0.54/0.72  thf('120', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((X0) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.72  thf('121', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((sk_A) = (k1_xboole_0))
% 0.54/0.72        | ((sk_F) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['119', '120'])).
% 0.54/0.72  thf('122', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['121'])).
% 0.54/0.72  thf('123', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('124', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('125', plain, (((sk_B) = (sk_F))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.54/0.72  thf('126', plain, (((sk_F) != (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['124', '125'])).
% 0.54/0.72  thf('127', plain, ($false),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['122', '123', '126'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
