%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WyZrJLa14v

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 186 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  972 (4768 expanded)
%              Number of equality atoms :  159 ( 734 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k2_mcart_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('4',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13','14'])).

thf('16',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( sk_I != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('21',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('28',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','26','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('41',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_F ),
    inference('sat_resolution*',[status(thm)],['18','38','55','56'])).

thf('58',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_F ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('61',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('65',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

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
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    sk_F != sk_F ),
    inference(demod,[status(thm)],['58','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WyZrJLa14v
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 50 iterations in 0.029s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_I_type, type, sk_I: $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
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
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.21/0.49         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
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
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) = (k1_xboole_0))
% 0.21/0.49          | ((k11_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14) = (k2_mcart_1 @ X14))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ sk_E))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d4_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.49       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.21/0.49           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.49  thf(t7_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, (((k2_mcart_1 @ sk_E) = (sk_I))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.49  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['10', '11', '12', '13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((sk_I) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) = (k1_xboole_0))
% 0.21/0.49          | ((k10_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14)
% 0.21/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X14)))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.21/0.49           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.49  thf(d3_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '26', '29'])).
% 0.21/0.49  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['30', '31', '32', '33', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((sk_H) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) = (k1_xboole_0))
% 0.21/0.49          | ((k9_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14)
% 0.21/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X14))))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42', '45', '46'])).
% 0.21/0.49  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['47', '48', '49', '50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((((sk_G) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.21/0.49       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))) | 
% 0.21/0.49       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.21/0.49       ~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['18', '38', '55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) = (k1_xboole_0))
% 0.21/0.49          | ((k8_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14)
% 0.21/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X14))))
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.49  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['65', '66', '67', '68', '69'])).
% 0.21/0.49  thf('71', plain, (((sk_F) != (sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '70'])).
% 0.21/0.49  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
