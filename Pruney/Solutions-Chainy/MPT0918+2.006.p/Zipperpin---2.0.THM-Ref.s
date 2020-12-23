%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9VCrW5ZsYp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 158 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  883 (4056 expanded)
%              Number of equality atoms :  147 ( 630 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ sk_F @ sk_G ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('18',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27','28'])).

thf('30',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( sk_I != sk_I ) ),
    inference(demod,[status(thm)],['15','29'])).

thf('31',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('34',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('37',plain,(
    ! [X13: $i,X15: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = sk_H ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( sk_H != sk_H )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(demod,[status(thm)],['31','45'])).

thf('47',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ sk_F @ sk_G ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('52',plain,(
    ! [X13: $i,X15: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('53',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( sk_G != sk_G ) ),
    inference(demod,[status(thm)],['47','58'])).

thf('60',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_F ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9VCrW5ZsYp
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 106 iterations in 0.034s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.48  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_I_type, type, sk_I: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.48  thf(t78_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.48              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.48                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.48                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.48                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.48                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.48          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48               ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48               ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.48                 ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.48                        ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.48                        ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.48                        ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.48                   ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t78_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t61_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ~( ![E:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.48                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.48                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.48                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.21/0.48                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X10) = (k1_xboole_0))
% 0.21/0.48          | ((k8_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11)
% 0.21/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X11))))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.21/0.48          | ((X12) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t31_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.48       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k4_mcart_1 @ X0 @ X1 @ X2 @ X3)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.21/0.48  thf(t7_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k1_mcart_1 @ (k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.21/0.48           = (k4_tarski @ X3 @ X2))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E)) = (k4_tarski @ sk_F @ sk_G))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '9', '10'])).
% 0.21/0.48  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.48        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X10) = (k1_xboole_0))
% 0.21/0.48          | ((k11_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11) = (k2_mcart_1 @ X11))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.21/0.48          | ((X12) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.48            = (k2_mcart_1 @ sk_E))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k4_mcart_1 @ X0 @ X1 @ X2 @ X3)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, (((k2_mcart_1 @ sk_E) = (sk_I))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '23'])).
% 0.21/0.48  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['24', '25', '26', '27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.48        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.48        | ((sk_I) != (sk_I)))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.48        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X10) = (k1_xboole_0))
% 0.21/0.48          | ((k10_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X11)))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.21/0.48          | ((X12) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k2_mcart_1 @ (k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))) = (X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_E)) = (sk_H))),
% 0.21/0.48      inference('sup+', [status(thm)], ['35', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '39'])).
% 0.21/0.48  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['40', '41', '42', '43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((((sk_H) != (sk_H))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.48        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X10) = (k1_xboole_0))
% 0.21/0.48          | ((k9_mcart_1 @ X8 @ X9 @ X10 @ X12 @ X11)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X11))))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X12))
% 0.21/0.48          | ((X12) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E)) = (k4_tarski @ sk_F @ sk_G))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.48  thf('54', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('56', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['53', '54', '55', '56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.48        | ((sk_G) != (sk_G)))),
% 0.21/0.48      inference('demod', [status(thm)], ['47', '58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))),
% 0.21/0.48      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.48  thf('61', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['11', '12', '13', '14', '60', '61'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
