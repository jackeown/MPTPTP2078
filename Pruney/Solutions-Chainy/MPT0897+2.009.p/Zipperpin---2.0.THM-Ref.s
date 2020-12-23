%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bvEuqVg5qN

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:41 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  161 (8698 expanded)
%              Number of leaves         :   20 (2570 expanded)
%              Depth                    :   45
%              Number of atoms          : 1817 (133285 expanded)
%              Number of equality atoms :  299 (19733 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X0 = X4 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X0 = X4 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_D = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    sk_D = sk_H ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','27'])).

thf('29',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_A = X2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = X2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('49',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('50',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_B = X1 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B = X1 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['46'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B = X1 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_G )
      = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(eq_res,[status(thm)],['55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['49','68'])).

thf('70',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('71',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B = sk_F )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['48','80'])).

thf('82',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['46'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('86',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = X2 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_F )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['85','98'])).

thf('100',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_F )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['99'])).

thf('101',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_F @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_F @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = X2 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','83','84','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_A = X2 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( sk_A = sk_E )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['106'])).

thf('108',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['108'])).

thf('110',plain,(
    sk_D = sk_H ),
    inference(eq_res,[status(thm)],['23'])).

thf('111',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['108'])).

thf('112',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['46'])).

thf('115',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['108'])).

thf('116',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    sk_B = sk_F ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('119',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['108'])).

thf('120',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['108'])).

thf('123',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['113','117','121','122'])).

thf('124',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['109','123'])).

thf('125',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['107','124'])).

thf('126',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('131',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_H = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != sk_H ),
    inference(demod,[status(thm)],['2','132'])).

thf('134',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('135',plain,(
    sk_H = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('136',plain,(
    sk_H = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('137',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ sk_H )
      = sk_H ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    sk_H != sk_H ),
    inference(demod,[status(thm)],['133','137'])).

thf('139',plain,(
    $false ),
    inference(simplify,[status(thm)],['138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bvEuqVg5qN
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:27:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.60/1.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.82  % Solved by: fo/fo7.sh
% 1.60/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.82  % done 1206 iterations in 1.355s
% 1.60/1.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.82  % SZS output start Refutation
% 1.60/1.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.82  thf(sk_H_type, type, sk_H: $i).
% 1.60/1.82  thf(sk_F_type, type, sk_F: $i).
% 1.60/1.82  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.60/1.82  thf(sk_E_type, type, sk_E: $i).
% 1.60/1.82  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.82  thf(sk_G_type, type, sk_G: $i).
% 1.60/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.82  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.82  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.60/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.82  thf(t57_mcart_1, conjecture,
% 1.60/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.60/1.82     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.60/1.82       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.60/1.82         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.60/1.82           ( ( D ) = ( H ) ) ) ) ))).
% 1.60/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.82    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.60/1.82        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.60/1.82          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.60/1.82            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.60/1.82              ( ( D ) = ( H ) ) ) ) ) )),
% 1.60/1.82    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 1.60/1.82  thf('0', plain,
% 1.60/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 1.60/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.82  thf('1', plain,
% 1.60/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.60/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.60/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.82  thf('2', plain,
% 1.60/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.60/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.60/1.82  thf(d4_zfmisc_1, axiom,
% 1.60/1.82    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.82     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.60/1.82       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.60/1.82  thf('3', plain,
% 1.60/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.60/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.60/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.60/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.60/1.82  thf(t195_relat_1, axiom,
% 1.60/1.82    (![A:$i,B:$i]:
% 1.60/1.82     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.60/1.82          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.60/1.82               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.60/1.82  thf('4', plain,
% 1.60/1.82      (![X0 : $i, X1 : $i]:
% 1.60/1.82         (((X0) = (k1_xboole_0))
% 1.60/1.82          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 1.60/1.82          | ((X1) = (k1_xboole_0)))),
% 1.60/1.82      inference('cnf', [status(esa)], [t195_relat_1])).
% 1.60/1.82  thf('5', plain,
% 1.60/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.82         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.60/1.82            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 1.60/1.82          | ((X0) = (k1_xboole_0))
% 1.60/1.82          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 1.60/1.82      inference('sup+', [status(thm)], ['3', '4'])).
% 1.60/1.82  thf('6', plain,
% 1.60/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.60/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.60/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.82  thf(d3_zfmisc_1, axiom,
% 1.60/1.82    (![A:$i,B:$i,C:$i]:
% 1.60/1.82     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.60/1.82       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.60/1.82  thf('7', plain,
% 1.60/1.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.60/1.82         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.60/1.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.60/1.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.60/1.82  thf('8', plain,
% 1.60/1.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.60/1.82         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.60/1.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.60/1.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.60/1.82  thf('9', plain,
% 1.60/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.60/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.60/1.82      inference('sup+', [status(thm)], ['7', '8'])).
% 1.60/1.82  thf('10', plain,
% 1.60/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.60/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.60/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.60/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.60/1.82  thf('11', plain,
% 1.60/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.60/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.60/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.60/1.82  thf('12', plain,
% 1.60/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.60/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.60/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.82  thf('13', plain,
% 1.60/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.60/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.60/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.60/1.82  thf(t37_mcart_1, axiom,
% 1.60/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.60/1.82     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.60/1.82       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 1.67/1.82         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 1.67/1.82  thf('14', plain,
% 1.67/1.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ X9 @ X10 @ X11) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k3_zfmisc_1 @ X12 @ X13 @ X14))
% 1.67/1.82          | ((X11) = (X14)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.67/1.82  thf('15', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((X0) = (X4))
% 1.67/1.82          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['13', '14'])).
% 1.67/1.82  thf('16', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('17', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((X0) = (X4))
% 1.67/1.82          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['15', '16'])).
% 1.67/1.82  thf('18', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 1.67/1.82          | ((sk_D) = (X0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['12', '17'])).
% 1.67/1.82  thf('19', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.82  thf('20', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((sk_D) = (X0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['18', '19'])).
% 1.67/1.82  thf('21', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('22', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((sk_D) = (X0)))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 1.67/1.82  thf('23', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((sk_D) = (X0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['11', '22'])).
% 1.67/1.82  thf('24', plain, (((sk_D) = (sk_H))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['23'])).
% 1.67/1.82  thf('25', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['6', '24'])).
% 1.67/1.82  thf('26', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.67/1.82            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 1.67/1.82          | ((X0) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['3', '4'])).
% 1.67/1.82  thf('27', plain,
% 1.67/1.82      ((((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.67/1.82          = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['25', '26'])).
% 1.67/1.82  thf('28', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 1.67/1.82          = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['5', '27'])).
% 1.67/1.82  thf('29', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 1.67/1.82            = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['28'])).
% 1.67/1.82  thf('30', plain,
% 1.67/1.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ X9 @ X10 @ X11) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k3_zfmisc_1 @ X12 @ X13 @ X14))
% 1.67/1.82          | ((X9) = (X12)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.67/1.82  thf('31', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82          | ((sk_A) = (X2))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['29', '30'])).
% 1.67/1.82  thf('32', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((sk_A) = (X2))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['31'])).
% 1.67/1.82  thf('33', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['6', '24'])).
% 1.67/1.82  thf('34', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('35', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['6', '24'])).
% 1.67/1.82  thf('36', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('37', plain,
% 1.67/1.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ X9 @ X10 @ X11) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k3_zfmisc_1 @ X12 @ X13 @ X14))
% 1.67/1.82          | ((X10) = (X13)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.67/1.82  thf('38', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((X1) = (X5))
% 1.67/1.82          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['36', '37'])).
% 1.67/1.82  thf('39', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('40', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((X1) = (X5))
% 1.67/1.82          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['38', '39'])).
% 1.67/1.82  thf('41', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((sk_C) = (X1)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['35', '40'])).
% 1.67/1.82  thf('42', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['6', '24'])).
% 1.67/1.82  thf('43', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((sk_C) = (X1)))),
% 1.67/1.82      inference('demod', [status(thm)], ['41', '42'])).
% 1.67/1.82  thf('44', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('45', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((sk_C) = (X1)))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 1.67/1.82  thf('46', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((sk_C) = (X1)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['34', '45'])).
% 1.67/1.82  thf('47', plain, (((sk_C) = (sk_G))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['46'])).
% 1.67/1.82  thf('48', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['33', '47'])).
% 1.67/1.82  thf('49', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['33', '47'])).
% 1.67/1.82  thf('50', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 1.67/1.82            = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['28'])).
% 1.67/1.82  thf('51', plain,
% 1.67/1.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ X9 @ X10 @ X11) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k3_zfmisc_1 @ X12 @ X13 @ X14))
% 1.67/1.82          | ((X10) = (X13)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.67/1.82  thf('52', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82          | ((sk_B) = (X1))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['50', '51'])).
% 1.67/1.82  thf('53', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((sk_B) = (X1))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['52'])).
% 1.67/1.82  thf('54', plain, (((sk_C) = (sk_G))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['46'])).
% 1.67/1.82  thf('55', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((sk_B) = (X1))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['53', '54'])).
% 1.67/1.82  thf('56', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['55'])).
% 1.67/1.82  thf('57', plain,
% 1.67/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.67/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.67/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.67/1.82  thf('58', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ X0)
% 1.67/1.82            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.67/1.82          | ((sk_B) = (sk_F))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['56', '57'])).
% 1.67/1.82  thf(t55_mcart_1, axiom,
% 1.67/1.82    (![A:$i,B:$i,C:$i,D:$i]:
% 1.67/1.82     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.67/1.82         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.67/1.82       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.67/1.82  thf('59', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 1.67/1.82         (((X17) != (k1_xboole_0))
% 1.67/1.82          | ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19) = (k1_xboole_0)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.67/1.82  thf('60', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X19 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X15 @ X16 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['59'])).
% 1.67/1.82  thf('61', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('62', plain,
% 1.67/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.67/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.67/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.67/1.82  thf('63', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 1.67/1.82           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.67/1.82      inference('sup+', [status(thm)], ['61', '62'])).
% 1.67/1.82  thf('64', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k1_xboole_0)
% 1.67/1.82           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 1.67/1.82      inference('sup+', [status(thm)], ['60', '63'])).
% 1.67/1.82  thf('65', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 1.67/1.82         (((X19) != (k1_xboole_0))
% 1.67/1.82          | ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19) = (k1_xboole_0)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.67/1.82  thf('66', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['65'])).
% 1.67/1.82  thf('67', plain,
% 1.67/1.82      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.67/1.82      inference('demod', [status(thm)], ['64', '66'])).
% 1.67/1.82  thf('68', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ X0) = (k1_xboole_0))
% 1.67/1.82          | ((sk_B) = (sk_F))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['58', '67'])).
% 1.67/1.82  thf('69', plain,
% 1.67/1.82      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['49', '68'])).
% 1.67/1.82  thf('70', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('71', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 1.67/1.82  thf('72', plain,
% 1.67/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.67/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.67/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.67/1.82  thf('73', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 1.67/1.82            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.67/1.82          | ((sk_B) = (sk_F))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['71', '72'])).
% 1.67/1.82  thf('74', plain,
% 1.67/1.82      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.67/1.82      inference('demod', [status(thm)], ['64', '66'])).
% 1.67/1.82  thf('75', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0))
% 1.67/1.82          | ((sk_B) = (sk_F))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['73', '74'])).
% 1.67/1.82  thf('76', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('77', plain,
% 1.67/1.82      ((((k1_xboole_0) != (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['75', '76'])).
% 1.67/1.82  thf('78', plain, ((((sk_B) = (sk_F)) | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['77'])).
% 1.67/1.82  thf('79', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['65'])).
% 1.67/1.82  thf('80', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['78', '79'])).
% 1.67/1.82  thf('81', plain,
% 1.67/1.82      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82        | ((sk_B) = (sk_F)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['48', '80'])).
% 1.67/1.82  thf('82', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('83', plain, (((sk_B) = (sk_F))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.67/1.82  thf('84', plain, (((sk_C) = (sk_G))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['46'])).
% 1.67/1.82  thf('85', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('86', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['33', '47'])).
% 1.67/1.82  thf('87', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('88', plain,
% 1.67/1.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ X9 @ X10 @ X11) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k3_zfmisc_1 @ X12 @ X13 @ X14))
% 1.67/1.82          | ((X9) = (X12)))),
% 1.67/1.82      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.67/1.82  thf('89', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 1.67/1.82          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.82  thf('90', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.67/1.82           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.67/1.82      inference('demod', [status(thm)], ['9', '10'])).
% 1.67/1.82  thf('91', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.67/1.82          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 1.67/1.82          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['89', '90'])).
% 1.67/1.82  thf('92', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['86', '91'])).
% 1.67/1.82  thf('93', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.67/1.82         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['33', '47'])).
% 1.67/1.82  thf('94', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.67/1.82      inference('demod', [status(thm)], ['92', '93'])).
% 1.67/1.82  thf('95', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('96', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.67/1.82  thf('97', plain, (((sk_B) = (sk_F))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.67/1.82  thf('98', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (X2)))),
% 1.67/1.82      inference('demod', [status(thm)], ['96', '97'])).
% 1.67/1.82  thf('99', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.67/1.82            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((k2_zfmisc_1 @ sk_A @ sk_F) = (k2_zfmisc_1 @ X3 @ X2)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['85', '98'])).
% 1.67/1.82  thf('100', plain,
% 1.67/1.82      (((k2_zfmisc_1 @ sk_A @ sk_F) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['99'])).
% 1.67/1.82  thf('101', plain,
% 1.67/1.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.67/1.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.67/1.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.67/1.82  thf('102', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ sk_A @ sk_F @ X0)
% 1.67/1.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 1.67/1.82      inference('sup+', [status(thm)], ['100', '101'])).
% 1.67/1.82  thf('103', plain,
% 1.67/1.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.67/1.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.67/1.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.67/1.82  thf('104', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         ((k3_zfmisc_1 @ sk_A @ sk_F @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 1.67/1.82      inference('demod', [status(thm)], ['102', '103'])).
% 1.67/1.82  thf('105', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((sk_A) = (X2))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['32', '83', '84', '104'])).
% 1.67/1.82  thf('106', plain,
% 1.67/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.82         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0))
% 1.67/1.82          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82          | ((sk_A) = (X2)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['105'])).
% 1.67/1.82  thf('107', plain,
% 1.67/1.82      ((((sk_A) = (sk_E))
% 1.67/1.82        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['106'])).
% 1.67/1.82  thf('108', plain,
% 1.67/1.82      ((((sk_A) != (sk_E))
% 1.67/1.82        | ((sk_B) != (sk_F))
% 1.67/1.82        | ((sk_C) != (sk_G))
% 1.67/1.82        | ((sk_D) != (sk_H)))),
% 1.67/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.82  thf('109', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.67/1.82      inference('split', [status(esa)], ['108'])).
% 1.67/1.82  thf('110', plain, (((sk_D) = (sk_H))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['23'])).
% 1.67/1.82  thf('111', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.67/1.82      inference('split', [status(esa)], ['108'])).
% 1.67/1.82  thf('112', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.67/1.82      inference('sup-', [status(thm)], ['110', '111'])).
% 1.67/1.82  thf('113', plain, ((((sk_D) = (sk_H)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['112'])).
% 1.67/1.82  thf('114', plain, (((sk_C) = (sk_G))),
% 1.67/1.82      inference('eq_res', [status(thm)], ['46'])).
% 1.67/1.82  thf('115', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.67/1.82      inference('split', [status(esa)], ['108'])).
% 1.67/1.82  thf('116', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.67/1.82      inference('sup-', [status(thm)], ['114', '115'])).
% 1.67/1.82  thf('117', plain, ((((sk_C) = (sk_G)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['116'])).
% 1.67/1.82  thf('118', plain, (((sk_B) = (sk_F))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.67/1.82  thf('119', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.67/1.82      inference('split', [status(esa)], ['108'])).
% 1.67/1.82  thf('120', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.67/1.82      inference('sup-', [status(thm)], ['118', '119'])).
% 1.67/1.82  thf('121', plain, ((((sk_B) = (sk_F)))),
% 1.67/1.82      inference('simplify', [status(thm)], ['120'])).
% 1.67/1.82  thf('122', plain,
% 1.67/1.82      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 1.67/1.82       ~ (((sk_D) = (sk_H)))),
% 1.67/1.82      inference('split', [status(esa)], ['108'])).
% 1.67/1.82  thf('123', plain, (~ (((sk_A) = (sk_E)))),
% 1.67/1.82      inference('sat_resolution*', [status(thm)], ['113', '117', '121', '122'])).
% 1.67/1.82  thf('124', plain, (((sk_A) != (sk_E))),
% 1.67/1.82      inference('simpl_trail', [status(thm)], ['109', '123'])).
% 1.67/1.82  thf('125', plain,
% 1.67/1.82      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 1.67/1.82        | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('simplify_reflect-', [status(thm)], ['107', '124'])).
% 1.67/1.82  thf('126', plain,
% 1.67/1.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.67/1.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.67/1.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.67/1.82  thf('127', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 1.67/1.82            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup+', [status(thm)], ['125', '126'])).
% 1.67/1.82  thf('128', plain,
% 1.67/1.82      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.67/1.82      inference('demod', [status(thm)], ['64', '66'])).
% 1.67/1.82  thf('129', plain,
% 1.67/1.82      (![X0 : $i]:
% 1.67/1.82         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0))
% 1.67/1.82          | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('demod', [status(thm)], ['127', '128'])).
% 1.67/1.82  thf('130', plain,
% 1.67/1.82      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.67/1.82      inference('demod', [status(thm)], ['0', '1'])).
% 1.67/1.82  thf('131', plain,
% 1.67/1.82      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (k1_xboole_0)))),
% 1.67/1.82      inference('sup-', [status(thm)], ['129', '130'])).
% 1.67/1.82  thf('132', plain, (((sk_H) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['131'])).
% 1.67/1.82  thf('133', plain, (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['2', '132'])).
% 1.67/1.82  thf('134', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['65'])).
% 1.67/1.82  thf('135', plain, (((sk_H) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['131'])).
% 1.67/1.82  thf('136', plain, (((sk_H) = (k1_xboole_0))),
% 1.67/1.82      inference('simplify', [status(thm)], ['131'])).
% 1.67/1.82  thf('137', plain,
% 1.67/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.82         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ sk_H) = (sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.67/1.82  thf('138', plain, (((sk_H) != (sk_H))),
% 1.67/1.82      inference('demod', [status(thm)], ['133', '137'])).
% 1.67/1.82  thf('139', plain, ($false), inference('simplify', [status(thm)], ['138'])).
% 1.67/1.82  
% 1.67/1.82  % SZS output end Refutation
% 1.67/1.82  
% 1.67/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
