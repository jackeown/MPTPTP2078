%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9JB2FLoTIO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:39 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  178 (2021 expanded)
%              Number of leaves         :   18 ( 588 expanded)
%              Depth                    :   50
%              Number of atoms          : 1800 (31236 expanded)
%              Number of equality atoms :  396 (6728 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('7',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X14 = X19 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('19',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(demod,[status(thm)],['17','19','20'])).

thf('22',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['30'])).

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
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( X11 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('40',plain,(
    ! [X10: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X10 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['45'])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['5','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['75','76','77'])).

thf('87',plain,(
    sk_H != k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','88'])).

thf('90',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ),
    inference(eq_res,[status(thm)],['89'])).

thf('91',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('101',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(condensation,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('109',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 )
      | ( sk_A = X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = sk_E )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['114'])).

thf('116',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['75','76','77'])).

thf('119',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['116'])).

thf('120',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('123',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('125',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(eq_res,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('134',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_G )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['116'])).

thf('140',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['110','111','112'])).

thf('143',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['116'])).

thf('144',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['116'])).

thf('147',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['121','141','145','146'])).

thf('148',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['117','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['115','148'])).

thf('150',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_F )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('152',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['110','111','112'])).

thf('157',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['153','154','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9JB2FLoTIO
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 636 iterations in 0.354s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.59/0.81  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.81  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.81  thf(sk_G_type, type, sk_G: $i).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(sk_F_type, type, sk_F: $i).
% 0.59/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.81  thf(sk_H_type, type, sk_H: $i).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.81  thf(d3_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.59/0.81       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('1', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.59/0.81      inference('sup+', [status(thm)], ['0', '1'])).
% 0.59/0.81  thf(d4_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.59/0.81       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf(t56_mcart_1, conjecture,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.81     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.59/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.59/0.81           ( ( D ) = ( H ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.81        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.59/0.81          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.59/0.81              ( ( D ) = ( H ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.59/0.81  thf('5', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf(t36_mcart_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.81     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.59/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         (((X14) = (k1_xboole_0))
% 0.59/0.81          | ((X15) = (k1_xboole_0))
% 0.59/0.81          | ((X16) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.59/0.81          | ((X14) = (X19)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((X4) = (X0))
% 0.59/0.81          | ((X6) = (k1_xboole_0))
% 0.59/0.81          | ((X5) = (k1_xboole_0))
% 0.59/0.81          | ((X4) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.59/0.81            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.59/0.81          | ((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X2) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['7', '10'])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.81            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.59/0.81          | ((X0) = (sk_D))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['6', '11'])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      ((((sk_H) = (k1_xboole_0))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('eq_res', [status(thm)], ['12'])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.59/0.81          | ((sk_H) = (sk_D))
% 0.59/0.81          | ((sk_G) = (k1_xboole_0))
% 0.59/0.81          | ((sk_H) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1)
% 0.59/0.81            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ X0) @ X1))
% 0.59/0.81          | ((sk_H) = (k1_xboole_0))
% 0.59/0.81          | ((sk_G) = (k1_xboole_0))
% 0.59/0.81          | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['15', '16'])).
% 0.59/0.81  thf(t35_mcart_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.81         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.59/0.81       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.59/0.81         (((X10) != (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X10 @ X11 @ X13) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      (![X11 : $i, X13 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13) = (k1_xboole_0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1))
% 0.59/0.81          | ((sk_H) = (k1_xboole_0))
% 0.59/0.81          | ((sk_G) = (k1_xboole_0))
% 0.59/0.81          | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('demod', [status(thm)], ['17', '19', '20'])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k1_xboole_0))
% 0.59/0.81          | ((X12) = (k1_xboole_0))
% 0.59/0.81          | ((X11) = (k1_xboole_0))
% 0.59/0.81          | ((X10) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.59/0.81        | ((sk_D) = (k1_xboole_0))
% 0.59/0.81        | ((sk_C) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['22', '25'])).
% 0.59/0.81  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('28', plain, (((sk_D) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['26', '27', '28'])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['21', '29'])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (k1_xboole_0))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.81  thf(t113_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (k1_xboole_0))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.81  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      ((((sk_H) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['34', '35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.59/0.81         (((X11) != (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X10 @ X11 @ X13) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X10 : $i, X13 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X10 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('43', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.81  thf('44', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['40', '43'])).
% 0.59/0.81  thf('45', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['44'])).
% 0.59/0.81  thf('46', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['45'])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['38', '46'])).
% 0.59/0.81  thf('48', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.59/0.81          | ((sk_H) = (sk_D))
% 0.59/0.81          | ((sk_G) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['37', '47'])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['26', '27', '28'])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['50'])).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('53', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.81  thf('54', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_G) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.81  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('57', plain, ((((sk_H) = (sk_D)) | ((sk_G) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.59/0.81  thf('58', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['45'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('60', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['58', '59'])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.59/0.81           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['60', '61'])).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      (![X11 : $i, X13 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13) = (k1_xboole_0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.81  thf('64', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.81  thf('65', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.81  thf('66', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['65'])).
% 0.59/0.81  thf('67', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['66'])).
% 0.59/0.81  thf('68', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '67'])).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['57', '68'])).
% 0.59/0.81  thf('70', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['26', '27', '28'])).
% 0.59/0.81  thf('71', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.81  thf('72', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['71'])).
% 0.59/0.81  thf('73', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('74', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_H) = (sk_D))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.81  thf('75', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['74'])).
% 0.59/0.81  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('78', plain, (((sk_H) = (sk_D))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['75', '76', '77'])).
% 0.59/0.81  thf('79', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.59/0.81      inference('demod', [status(thm)], ['5', '78'])).
% 0.59/0.81  thf('80', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('81', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         (((X14) = (k1_xboole_0))
% 0.59/0.81          | ((X15) = (k1_xboole_0))
% 0.59/0.81          | ((X16) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.59/0.81          | ((X16) = (X17)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.59/0.81  thf('82', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['80', '81'])).
% 0.59/0.81  thf('83', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((sk_H) = (k1_xboole_0))
% 0.59/0.81          | ((sk_C) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['79', '82'])).
% 0.59/0.81  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('85', plain, (((sk_D) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('86', plain, (((sk_H) = (sk_D))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['75', '76', '77'])).
% 0.59/0.81  thf('87', plain, (((sk_H) != (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['85', '86'])).
% 0.59/0.81  thf('88', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['83', '84', '87'])).
% 0.59/0.81  thf('89', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['4', '88'])).
% 0.59/0.81  thf('90', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 0.59/0.81      inference('eq_res', [status(thm)], ['89'])).
% 0.59/0.81  thf('91', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('92', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['90', '91'])).
% 0.59/0.81  thf('93', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.81  thf('94', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['92', '93'])).
% 0.59/0.81  thf('95', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         (((X14) = (k1_xboole_0))
% 0.59/0.81          | ((X15) = (k1_xboole_0))
% 0.59/0.81          | ((X16) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.59/0.81          | ((X16) = (X17)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.59/0.81  thf('96', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (X3))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.81  thf('97', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('99', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (X3))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['96', '97', '98'])).
% 0.59/0.81  thf('100', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['92', '93'])).
% 0.59/0.81  thf('101', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         (((X14) = (k1_xboole_0))
% 0.59/0.81          | ((X15) = (k1_xboole_0))
% 0.59/0.81          | ((X16) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.59/0.81          | ((X15) = (X18)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.59/0.81  thf('102', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_B) = (X2))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['100', '101'])).
% 0.59/0.81  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('105', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_B) = (X2))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['102', '103', '104'])).
% 0.59/0.81  thf('106', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_B) = (sk_F))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('eq_res', [status(thm)], ['105'])).
% 0.59/0.81  thf('107', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.59/0.81      inference('condensation', [status(thm)], ['106'])).
% 0.59/0.81  thf('108', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('109', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (sk_F))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['107', '108'])).
% 0.59/0.81  thf('110', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['109'])).
% 0.59/0.81  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('112', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('113', plain, (((sk_B) = (sk_F))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['110', '111', '112'])).
% 0.59/0.81  thf('114', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (X3))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['99', '113'])).
% 0.59/0.81  thf('115', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (sk_E))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0)))),
% 0.59/0.81      inference('eq_res', [status(thm)], ['114'])).
% 0.59/0.81  thf('116', plain,
% 0.59/0.81      ((((sk_A) != (sk_E))
% 0.59/0.81        | ((sk_B) != (sk_F))
% 0.59/0.81        | ((sk_C) != (sk_G))
% 0.59/0.81        | ((sk_D) != (sk_H)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('117', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.59/0.81      inference('split', [status(esa)], ['116'])).
% 0.59/0.81  thf('118', plain, (((sk_H) = (sk_D))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['75', '76', '77'])).
% 0.59/0.81  thf('119', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.59/0.81      inference('split', [status(esa)], ['116'])).
% 0.59/0.81  thf('120', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['118', '119'])).
% 0.59/0.81  thf('121', plain, ((((sk_D) = (sk_H)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['120'])).
% 0.59/0.81  thf('122', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('123', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('124', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.59/0.81           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('125', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         (((X14) = (k1_xboole_0))
% 0.59/0.81          | ((X15) = (k1_xboole_0))
% 0.59/0.81          | ((X16) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.59/0.81          | ((X15) = (X18)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.59/0.81  thf('126', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.59/0.81          | ((X1) = (X5))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['124', '125'])).
% 0.59/0.81  thf('127', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((sk_D) = (k1_xboole_0))
% 0.59/0.81          | ((sk_C) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_C) = (X1)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['123', '126'])).
% 0.59/0.81  thf('128', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('129', plain, (((sk_D) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('130', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | ((sk_C) = (X1)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['127', '128', '129'])).
% 0.59/0.81  thf('131', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.59/0.81            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81          | ((sk_C) = (X1))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['122', '130'])).
% 0.59/0.81  thf('132', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.59/0.81      inference('eq_res', [status(thm)], ['131'])).
% 0.59/0.81  thf('133', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('134', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_C) = (sk_G))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.81  thf('135', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['134'])).
% 0.59/0.81  thf('136', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('137', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('138', plain, (((sk_C) = (sk_G))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['135', '136', '137'])).
% 0.59/0.81  thf('139', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.59/0.81      inference('split', [status(esa)], ['116'])).
% 0.59/0.81  thf('140', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['138', '139'])).
% 0.59/0.81  thf('141', plain, ((((sk_C) = (sk_G)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['140'])).
% 0.59/0.81  thf('142', plain, (((sk_B) = (sk_F))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['110', '111', '112'])).
% 0.59/0.81  thf('143', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.59/0.81      inference('split', [status(esa)], ['116'])).
% 0.59/0.81  thf('144', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['142', '143'])).
% 0.59/0.81  thf('145', plain, ((((sk_B) = (sk_F)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['144'])).
% 0.59/0.81  thf('146', plain,
% 0.59/0.81      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.59/0.81       ~ (((sk_D) = (sk_H)))),
% 0.59/0.81      inference('split', [status(esa)], ['116'])).
% 0.59/0.81  thf('147', plain, (~ (((sk_A) = (sk_E)))),
% 0.59/0.81      inference('sat_resolution*', [status(thm)], ['121', '141', '145', '146'])).
% 0.59/0.81  thf('148', plain, (((sk_A) != (sk_E))),
% 0.59/0.81      inference('simpl_trail', [status(thm)], ['117', '147'])).
% 0.59/0.81  thf('149', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['115', '148'])).
% 0.59/0.81  thf('150', plain, (((k2_zfmisc_1 @ sk_A @ sk_F) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['149'])).
% 0.59/0.81  thf('151', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.81  thf('152', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_F) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['150', '151'])).
% 0.59/0.81  thf('153', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['152'])).
% 0.59/0.81  thf('154', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('155', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('156', plain, (((sk_B) = (sk_F))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['110', '111', '112'])).
% 0.59/0.81  thf('157', plain, (((sk_F) != (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['155', '156'])).
% 0.59/0.81  thf('158', plain, ($false),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['153', '154', '157'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
