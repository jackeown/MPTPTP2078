%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nyNH0zInqJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 200 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          : 1286 (6588 expanded)
%              Number of equality atoms :  213 (1034 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(t78_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ? [F: $i,G: $i,H: $i,I: $i] :
              ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = F )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = G )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = H )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = I ) )
              & ( E
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ~ ( ( A != k1_xboole_0 )
            & ( B != k1_xboole_0 )
            & ( C != k1_xboole_0 )
            & ( D != k1_xboole_0 )
            & ? [F: $i,G: $i,H: $i,I: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                      = F )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                      = G )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                      = H )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                      = I ) )
                & ( E
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X17 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ? [E: $i] :
            ( ? [F: $i,G: $i,H: $i,I: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                      = F )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                      = G )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                      = H )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                      = I ) )
                & ( E
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) )
            & ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X15
       != ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
      | ( ( k11_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( ( k11_mcart_1 @ X8 @ X9 @ X10 @ X16 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
        = X14 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['7','20'])).

thf('22',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X15
       != ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
      | ( ( k9_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15 )
        = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( ( k9_mcart_1 @ X8 @ X9 @ X10 @ X16 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
        = X12 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

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
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('40',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X15
       != ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
      | ( ( k8_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15 )
        = X11 )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( ( k8_mcart_1 @ X8 @ X9 @ X10 @ X16 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
        = X11 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['22'])).

thf('56',plain,
    ( ( sk_F != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X15
       != ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
      | ( ( k10_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15 )
        = X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16 ) )
      | ( ( k10_mcart_1 @ X8 @ X9 @ X10 @ X16 @ ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 ) )
        = X13 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference('simplify_reflect-',[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['22'])).

thf('72',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('75',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_I ),
    inference('sat_resolution*',[status(thm)],['41','57','73','74'])).

thf('76',plain,(
    ( k2_mcart_1 @ sk_E )
 != sk_I ),
    inference(simpl_trail,[status(thm)],['25','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nyNH0zInqJ
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 46 iterations in 0.026s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_I_type, type, sk_I: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(t78_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.49              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.49                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.49                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.49                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.49                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.49          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49               ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49               ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.49                 ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.49                        ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.49                        ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.49                        ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.49                   ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t78_mcart_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t61_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![E:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.49                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.49                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.49                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.21/0.49                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (((X17) = (k1_xboole_0))
% 0.21/0.49          | ((X18) = (k1_xboole_0))
% 0.21/0.49          | ((X19) = (k1_xboole_0))
% 0.21/0.49          | ((k11_mcart_1 @ X17 @ X18 @ X19 @ X21 @ X20) = (k2_mcart_1 @ X20))
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X17 @ X18 @ X19 @ X21))
% 0.21/0.49          | ((X21) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ sk_E))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t59_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ?[E:$i]:
% 0.21/0.49            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.49                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.49                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.49                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.49                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.49                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.21/0.49              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X15 : $i, X16 : $i]:
% 0.21/0.49         (((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X15) != (k4_mcart_1 @ X11 @ X12 @ X13 @ X14))
% 0.21/0.49          | ((k11_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15) = (X14))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X16 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X11 @ X12 @ X13 @ X14) @ 
% 0.21/0.49               (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((k11_mcart_1 @ X8 @ X9 @ X10 @ X16 @ 
% 0.21/0.49              (k4_mcart_1 @ X11 @ X12 @ X13 @ X14)) = (X14))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_I))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.49  thf('13', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_I))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['15', '16', '17', '18', '19'])).
% 0.21/0.49  thf('21', plain, (((k2_mcart_1 @ sk_E) = (sk_I))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_E) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X15 : $i, X16 : $i]:
% 0.21/0.49         (((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X15) != (k4_mcart_1 @ X11 @ X12 @ X13 @ X14))
% 0.21/0.49          | ((k9_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15) = (X12))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X16 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X11 @ X12 @ X13 @ X14) @ 
% 0.21/0.49               (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((k9_mcart_1 @ X8 @ X9 @ X10 @ X16 @ 
% 0.21/0.49              (k4_mcart_1 @ X11 @ X12 @ X13 @ X14)) = (X12))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_G))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.49  thf('31', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_G))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.49  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['33', '34', '35', '36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((sk_G) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X15 : $i, X16 : $i]:
% 0.21/0.49         (((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X15) != (k4_mcart_1 @ X11 @ X12 @ X13 @ X14))
% 0.21/0.49          | ((k8_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15) = (X11))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X16 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X11 @ X12 @ X13 @ X14) @ 
% 0.21/0.49               (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((k8_mcart_1 @ X8 @ X9 @ X10 @ X16 @ 
% 0.21/0.49              (k4_mcart_1 @ X11 @ X12 @ X13 @ X14)) = (X11))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_F))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.49  thf('47', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_F))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.49  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['49', '50', '51', '52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.21/0.49         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((((sk_F) != (sk_F)))
% 0.21/0.49         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X15 : $i, X16 : $i]:
% 0.21/0.49         (((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X15) != (k4_mcart_1 @ X11 @ X12 @ X13 @ X14))
% 0.21/0.49          | ((k10_mcart_1 @ X8 @ X9 @ X10 @ X16 @ X15) = (X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.21/0.49         X16 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X11 @ X12 @ X13 @ X14) @ 
% 0.21/0.49               (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X16))
% 0.21/0.49          | ((k10_mcart_1 @ X8 @ X9 @ X10 @ X16 @ 
% 0.21/0.49              (k4_mcart_1 @ X11 @ X12 @ X13 @ X14)) = (X13))
% 0.21/0.49          | ((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X9) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_H))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '61'])).
% 0.21/0.49  thf('63', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_H))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['58', '64'])).
% 0.21/0.49  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['65', '66', '67', '68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((((sk_H) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))) | 
% 0.21/0.49       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.21/0.49       ~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.21/0.49       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['41', '57', '73', '74'])).
% 0.21/0.49  thf('76', plain, (((k2_mcart_1 @ sk_E) != (sk_I))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['25', '75'])).
% 0.21/0.49  thf('77', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['21', '76'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
