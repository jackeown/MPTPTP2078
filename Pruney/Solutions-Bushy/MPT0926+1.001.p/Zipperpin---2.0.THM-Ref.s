%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0926+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.45KfT8LQFw

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 212 expanded)
%              Number of leaves         :   21 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          : 1215 (10593 expanded)
%              Number of equality atoms :  184 (1491 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_J_type,type,(
    sk_J: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t86_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ( E != k1_xboole_0 )
        & ( F != k1_xboole_0 )
        & ( G != k1_xboole_0 )
        & ( H != k1_xboole_0 )
        & ? [I: $i] :
            ( ? [J: $i] :
                ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k8_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k9_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k9_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k10_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k10_mcart_1 @ E @ F @ G @ H @ J ) )
                    & ( ( k11_mcart_1 @ A @ B @ C @ D @ I )
                      = ( k11_mcart_1 @ E @ F @ G @ H @ J ) ) )
                & ( I = J )
                & ( m1_subset_1 @ J @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) )
            & ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ( E != k1_xboole_0 )
          & ( F != k1_xboole_0 )
          & ( G != k1_xboole_0 )
          & ( H != k1_xboole_0 )
          & ? [I: $i] :
              ( ? [J: $i] :
                  ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ I )
                        = ( k8_mcart_1 @ E @ F @ G @ H @ J ) )
                      & ( ( k9_mcart_1 @ A @ B @ C @ D @ I )
                        = ( k9_mcart_1 @ E @ F @ G @ H @ J ) )
                      & ( ( k10_mcart_1 @ A @ B @ C @ D @ I )
                        = ( k10_mcart_1 @ E @ F @ G @ H @ J ) )
                      & ( ( k11_mcart_1 @ A @ B @ C @ D @ I )
                        = ( k11_mcart_1 @ E @ F @ G @ H @ J ) ) )
                  & ( I = J )
                  & ( m1_subset_1 @ J @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) )
              & ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_J @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_I = sk_J ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X3 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('4',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_G != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_H != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_J ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_J ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_J ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_J ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_I = sk_J ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_I = sk_J ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_I = sk_J ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('16',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
    = ( k2_mcart_1 @ sk_I ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    sk_I = sk_J ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('25',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_G != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_H != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
    = ( k2_mcart_1 @ sk_I ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k2_mcart_1 @ sk_I )
     != ( k2_mcart_1 @ sk_I ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','21','22','30'])).

thf('32',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('35',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) )
     != ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('44',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_G != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_H != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('51',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X3 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('54',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
     != ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(demod,[status(thm)],['51','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X3 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('63',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_G != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_H != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
     != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference(demod,[status(thm)],['60','68'])).

thf('70',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
 != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X0 @ X1 @ X2 @ X4 @ X3 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X3 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('73',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
 != ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['70','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','79'])).


%------------------------------------------------------------------------------
