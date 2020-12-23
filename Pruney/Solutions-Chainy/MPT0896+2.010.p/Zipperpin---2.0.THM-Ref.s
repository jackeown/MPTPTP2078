%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uxIhGheT10

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:40 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  135 (1191 expanded)
%              Number of leaves         :   19 ( 354 expanded)
%              Depth                    :   39
%              Number of atoms          : 1400 (20203 expanded)
%              Number of equality atoms :  269 (4479 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,
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

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X13 @ X12 @ X11 )
       != ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) )
      | ( X11 = X16 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('25',plain,(
    ! [X7: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ k1_xboole_0 ) @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('45',plain,(
    ! [X23: $i,X24: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ X23 @ X24 @ k1_xboole_0 @ X27 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
       != ( k3_zfmisc_1 @ X20 @ X21 @ X22 ) )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','49'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','60'])).

thf('62',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X13 @ X12 @ X11 )
       != ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(eq_res,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['48'])).

thf('76',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['73'])).

thf('77',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('80',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','49'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
       != ( k3_zfmisc_1 @ X20 @ X21 @ X22 ) )
      | ( X18 = X21 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','49'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['73'])).

thf('94',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('97',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X13 @ X12 @ X11 )
       != ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(eq_res,[status(thm)],['101'])).

thf('103',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['73'])).

thf('107',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['73'])).

thf('110',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['78','95','108','109'])).

thf('111',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['74','110'])).

thf('112',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['72','111'])).

thf('113',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['7','112'])).

thf('114',plain,(
    $false ),
    inference(simplify,[status(thm)],['113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uxIhGheT10
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 629 iterations in 0.277s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.74  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.53/0.74  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(sk_G_type, type, sk_G: $i).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.74  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.53/0.74  thf(sk_H_type, type, sk_H: $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(t56_mcart_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.53/0.74     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.53/0.74           ( ( D ) = ( H ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.53/0.74        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.53/0.74          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.53/0.74              ( ( D ) = ( H ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t55_mcart_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.74         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.53/0.74       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26) != (k1_xboole_0))
% 0.53/0.74          | ((X26) = (k1_xboole_0))
% 0.53/0.74          | ((X25) = (k1_xboole_0))
% 0.53/0.74          | ((X24) = (k1_xboole_0))
% 0.53/0.74          | ((X23) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.53/0.74        | ((sk_A) = (k1_xboole_0))
% 0.53/0.74        | ((sk_B) = (k1_xboole_0))
% 0.53/0.74        | ((sk_C) = (k1_xboole_0))
% 0.53/0.74        | ((sk_D) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.74  thf('3', plain, (((sk_D) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('4', plain, (((sk_C) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf(d3_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.53/0.74       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.53/0.74           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.53/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf(d4_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.53/0.74       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.53/0.74           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.53/0.74      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf(t36_mcart_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.74     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.74         (((X11) = (k1_xboole_0))
% 0.53/0.74          | ((X12) = (k1_xboole_0))
% 0.53/0.74          | ((X13) = (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X13 @ X12 @ X11) != (k3_zfmisc_1 @ X14 @ X15 @ X16))
% 0.53/0.74          | ((X11) = (X16)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((X4) = (X0))
% 0.53/0.74          | ((X6) = (k1_xboole_0))
% 0.53/0.74          | ((X5) = (k1_xboole_0))
% 0.53/0.74          | ((X4) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.53/0.74            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.53/0.74          | ((X0) = (k1_xboole_0))
% 0.53/0.74          | ((X1) = (k1_xboole_0))
% 0.53/0.74          | ((X2) = (k1_xboole_0))
% 0.53/0.74          | ((X0) = (sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['15', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.53/0.74          | ((X0) = (sk_D))
% 0.53/0.74          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.53/0.74          | ((X1) = (k1_xboole_0))
% 0.53/0.74          | ((X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '19'])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      ((((sk_H) = (k1_xboole_0))
% 0.53/0.74        | ((sk_G) = (k1_xboole_0))
% 0.53/0.74        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 0.53/0.74        | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.53/0.74          | ((sk_H) = (sk_D))
% 0.53/0.74          | ((sk_G) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['21', '22'])).
% 0.53/0.74  thf(t35_mcart_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.74         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.53/0.74       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.53/0.74         (((X8) != (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X7 : $i, X10 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.53/0.74           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.53/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ k1_xboole_0) @ X1 @ X0)
% 0.53/0.74           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X7 : $i, X10 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (sk_D))
% 0.53/0.74          | ((sk_G) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['23', '29'])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.53/0.74           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.53/0.74      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 0.53/0.74            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.53/0.74          | ((sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((sk_G) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((sk_G) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('demod', [status(thm)], ['32', '33'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74        | ((sk_H) = (sk_D))
% 0.53/0.74        | ((sk_G) = (k1_xboole_0))
% 0.53/0.74        | ((sk_H) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      ((((sk_H) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['36'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.53/0.74         (((X27) != (k1_xboole_0))
% 0.53/0.74          | ((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X23 @ X24 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['38'])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (sk_D))
% 0.53/0.74          | ((sk_G) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['37', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74        | ((sk_G) = (k1_xboole_0))
% 0.53/0.74        | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.74  thf('43', plain, ((((sk_H) = (sk_D)) | ((sk_G) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.53/0.74         (((X25) != (k1_xboole_0))
% 0.53/0.74          | ((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X27 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X23 @ X24 @ k1_xboole_0 @ X27) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.53/0.74          | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['43', '45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('48', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.53/0.74  thf('49', plain, (((sk_H) = (sk_D))),
% 0.53/0.74      inference('simplify', [status(thm)], ['48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '49'])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf(t37_mcart_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.74     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.53/0.74       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ X17 @ X18 @ X19) = (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X17 @ X18 @ X19) != (k3_zfmisc_1 @ X20 @ X21 @ X22))
% 0.53/0.74          | ((X17) = (X20)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.53/0.74          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.53/0.74          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.53/0.74          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.53/0.74          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['53', '54'])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['50', '55'])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '49'])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.53/0.74      inference('demod', [status(thm)], ['56', '57'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.53/0.74  thf('61', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['12', '60'])).
% 0.53/0.74  thf('62', plain,
% 0.53/0.74      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['61'])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.74  thf('64', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['62', '63'])).
% 0.53/0.74  thf('65', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.53/0.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.74  thf('66', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['64', '65'])).
% 0.53/0.74  thf('67', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.74         (((X11) = (k1_xboole_0))
% 0.53/0.74          | ((X12) = (k1_xboole_0))
% 0.53/0.74          | ((X13) = (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X13 @ X12 @ X11) != (k3_zfmisc_1 @ X14 @ X15 @ X16))
% 0.53/0.74          | ((X13) = (X14)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.53/0.74          | ((sk_A) = (X3))
% 0.53/0.74          | ((sk_A) = (k1_xboole_0))
% 0.53/0.74          | ((sk_B) = (k1_xboole_0))
% 0.53/0.74          | ((X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.74  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('71', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.53/0.74          | ((sk_A) = (X3))
% 0.53/0.74          | ((X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['68', '69', '70'])).
% 0.53/0.74  thf('72', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (sk_E)))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['71'])).
% 0.53/0.74  thf('73', plain,
% 0.53/0.74      ((((sk_A) != (sk_E))
% 0.53/0.74        | ((sk_B) != (sk_F))
% 0.53/0.74        | ((sk_C) != (sk_G))
% 0.53/0.74        | ((sk_D) != (sk_H)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('74', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.53/0.74      inference('split', [status(esa)], ['73'])).
% 0.53/0.74  thf('75', plain, (((sk_H) = (sk_D))),
% 0.53/0.74      inference('simplify', [status(thm)], ['48'])).
% 0.53/0.74  thf('76', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.53/0.74      inference('split', [status(esa)], ['73'])).
% 0.53/0.74  thf('77', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['75', '76'])).
% 0.53/0.74  thf('78', plain, ((((sk_D) = (sk_H)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['77'])).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '49'])).
% 0.53/0.74  thf('81', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('82', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ X17 @ X18 @ X19) = (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X17 @ X18 @ X19) != (k3_zfmisc_1 @ X20 @ X21 @ X22))
% 0.53/0.74          | ((X18) = (X21)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.53/0.74  thf('83', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.53/0.74          | ((X1) = (X5))
% 0.53/0.74          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['81', '82'])).
% 0.53/0.74  thf('84', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.53/0.74           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('85', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.53/0.74          | ((X1) = (X5))
% 0.53/0.74          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['83', '84'])).
% 0.53/0.74  thf('86', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((sk_C) = (X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['80', '85'])).
% 0.53/0.74  thf('87', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.53/0.74         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '49'])).
% 0.53/0.74  thf('88', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.53/0.74          | ((sk_C) = (X1)))),
% 0.53/0.74      inference('demod', [status(thm)], ['86', '87'])).
% 0.53/0.74  thf('89', plain,
% 0.53/0.74      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('90', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((sk_C) = (X1)))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.53/0.74  thf('91', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.53/0.74            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.53/0.74          | ((sk_C) = (X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['79', '90'])).
% 0.53/0.74  thf('92', plain, (((sk_C) = (sk_G))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['91'])).
% 0.53/0.74  thf('93', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.53/0.74      inference('split', [status(esa)], ['73'])).
% 0.53/0.74  thf('94', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['92', '93'])).
% 0.53/0.74  thf('95', plain, ((((sk_C) = (sk_G)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['94'])).
% 0.53/0.74  thf('96', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['64', '65'])).
% 0.53/0.74  thf('97', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.74         (((X11) = (k1_xboole_0))
% 0.53/0.74          | ((X12) = (k1_xboole_0))
% 0.53/0.74          | ((X13) = (k1_xboole_0))
% 0.53/0.74          | ((k3_zfmisc_1 @ X13 @ X12 @ X11) != (k3_zfmisc_1 @ X14 @ X15 @ X16))
% 0.53/0.74          | ((X12) = (X15)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.53/0.74  thf('98', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.53/0.74          | ((sk_B) = (X2))
% 0.53/0.74          | ((sk_A) = (k1_xboole_0))
% 0.53/0.74          | ((sk_B) = (k1_xboole_0))
% 0.53/0.74          | ((X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['96', '97'])).
% 0.53/0.74  thf('99', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('101', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.53/0.74          | ((sk_B) = (X2))
% 0.53/0.74          | ((X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['98', '99', '100'])).
% 0.53/0.74  thf('102', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['101'])).
% 0.53/0.74  thf('103', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('104', plain, (![X0 : $i]: (((sk_A) != (X0)) | ((sk_B) = (sk_F)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['102', '103'])).
% 0.53/0.74  thf('105', plain, (((sk_B) = (sk_F))),
% 0.53/0.74      inference('simplify', [status(thm)], ['104'])).
% 0.53/0.74  thf('106', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.53/0.74      inference('split', [status(esa)], ['73'])).
% 0.53/0.74  thf('107', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['105', '106'])).
% 0.53/0.74  thf('108', plain, ((((sk_B) = (sk_F)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['107'])).
% 0.53/0.74  thf('109', plain,
% 0.53/0.74      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.53/0.74       ~ (((sk_D) = (sk_H)))),
% 0.53/0.74      inference('split', [status(esa)], ['73'])).
% 0.53/0.74  thf('110', plain, (~ (((sk_A) = (sk_E)))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['78', '95', '108', '109'])).
% 0.53/0.74  thf('111', plain, (((sk_A) != (sk_E))),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['74', '110'])).
% 0.53/0.74  thf('112', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['72', '111'])).
% 0.53/0.74  thf('113', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['7', '112'])).
% 0.53/0.74  thf('114', plain, ($false), inference('simplify', [status(thm)], ['113'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
