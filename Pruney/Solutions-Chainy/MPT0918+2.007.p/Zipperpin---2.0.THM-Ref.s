%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uGEADjbCUR

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 175 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  843 (4886 expanded)
%              Number of equality atoms :  107 ( 727 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf('#_fresh_sk4_type',type,(
    '#_fresh_sk4': $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X12
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k9_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k10_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k11_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('4',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7','8'])).

thf(t33_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X7 = X4 )
      | ( ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 )
       != ( k4_mcart_1 @ X0 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('11',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X7 ) ),
    inference(inj_rec,[status(thm)],['10'])).

thf('12',plain,
    ( ( '#_fresh_sk4' @ sk_E )
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X7 ) ),
    inference(inj_rec,[status(thm)],['10'])).

thf('15',plain,
    ( ( '#_fresh_sk4' @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_I
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_I != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(demod,[status(thm)],['1','16'])).

thf('18',plain,
    ( $false
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7','8'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 = X2 )
      | ( ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 )
       != ( k4_mcart_1 @ X0 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('21',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X5 ) ),
    inference(inj_rec,[status(thm)],['20'])).

thf('22',plain,
    ( ( '#_fresh_sk2' @ sk_E )
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X5 ) ),
    inference(inj_rec,[status(thm)],['20'])).

thf('25',plain,
    ( ( '#_fresh_sk2' @ sk_E )
    = sk_G ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_G
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7','8'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X1 = X0 )
      | ( ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 )
       != ( k4_mcart_1 @ X0 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('32',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['31'])).

thf('33',plain,
    ( ( '#_fresh_sk1' @ sk_E )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['31'])).

thf('36',plain,
    ( ( '#_fresh_sk1' @ sk_E )
    = sk_F ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_F
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( sk_F != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7','8'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6 = X3 )
      | ( ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 )
       != ( k4_mcart_1 @ X0 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('43',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X6 ) ),
    inference(inj_rec,[status(thm)],['42'])).

thf('44',plain,
    ( ( '#_fresh_sk3' @ sk_E )
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X1: $i,X5: $i,X6: $i,X7: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X1 @ X5 @ X6 @ X7 ) )
      = X6 ) ),
    inference(inj_rec,[status(thm)],['42'])).

thf('47',plain,
    ( ( '#_fresh_sk3' @ sk_E )
    = sk_H ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_H
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_I ),
    inference('sat_resolution*',[status(thm)],['29','40','51','52'])).

thf('54',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['18','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uGEADjbCUR
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 39 iterations in 0.021s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf('#_fresh_sk4_type', type, '#_fresh_sk4': $i > $i).
% 0.20/0.51  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf('#_fresh_sk3_type', type, '#_fresh_sk3': $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.51  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.20/0.51  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_I_type, type, sk_I: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(t78_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.51              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.51                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.51                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.51                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.51                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.51          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51               ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51               ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.51                 ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.51                        ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.51                        ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.51                        ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.51                   ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t78_mcart_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.20/0.51        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.20/0.51        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.20/0.51        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.20/0.51         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t60_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![E:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.51                 ( ( E ) =
% 0.20/0.51                   ( k4_mcart_1 @
% 0.20/0.51                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.51                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.51                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.51                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (((X8) = (k1_xboole_0))
% 0.20/0.51          | ((X9) = (k1_xboole_0))
% 0.20/0.51          | ((X10) = (k1_xboole_0))
% 0.20/0.51          | ((X12)
% 0.20/0.51              = (k4_mcart_1 @ (k8_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.20/0.51                 (k9_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.20/0.51                 (k10_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.20/0.51                 (k11_mcart_1 @ X8 @ X9 @ X10 @ X11 @ X12)))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11))
% 0.20/0.51          | ((X11) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((((sk_D) = (k1_xboole_0))
% 0.20/0.51        | ((sk_E)
% 0.20/0.51            = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((sk_E)
% 0.20/0.51         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.51  thf(t33_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.51     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.51       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.51         ( ( D ) = ( H ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (((X7) = (X4))
% 0.20/0.51          | ((k4_mcart_1 @ X1 @ X5 @ X6 @ X7)
% 0.20/0.51              != (k4_mcart_1 @ X0 @ X2 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk4' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X7))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((('#_fresh_sk4' @ sk_E)
% 0.20/0.51         = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.51  thf('13', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk4' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X7))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['10'])).
% 0.20/0.51  thf('15', plain, ((('#_fresh_sk4' @ sk_E) = (sk_I))),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((sk_I) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((sk_I) != (sk_I)))
% 0.20/0.51         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (($false)
% 0.20/0.51         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((sk_E)
% 0.20/0.51         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (((X5) = (X2))
% 0.20/0.51          | ((k4_mcart_1 @ X1 @ X5 @ X6 @ X7)
% 0.20/0.51              != (k4_mcart_1 @ X0 @ X2 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk2' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X5))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((('#_fresh_sk2' @ sk_E)
% 0.20/0.51         = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('sup+', [status(thm)], ['19', '21'])).
% 0.20/0.51  thf('23', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk2' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X5))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['20'])).
% 0.20/0.51  thf('25', plain, ((('#_fresh_sk2' @ sk_E) = (sk_G))),
% 0.20/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((sk_G) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.20/0.51         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((sk_G) != (sk_G)))
% 0.20/0.51         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((sk_E)
% 0.20/0.51         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (((X1) = (X0))
% 0.20/0.51          | ((k4_mcart_1 @ X1 @ X5 @ X6 @ X7)
% 0.20/0.51              != (k4_mcart_1 @ X0 @ X2 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk1' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X1))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((('#_fresh_sk1' @ sk_E)
% 0.20/0.51         = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '32'])).
% 0.20/0.51  thf('34', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk1' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X1))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['31'])).
% 0.20/0.51  thf('36', plain, ((('#_fresh_sk1' @ sk_E) = (sk_F))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((sk_F) = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.20/0.51         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((sk_F) != (sk_F)))
% 0.20/0.51         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((sk_E)
% 0.20/0.51         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.51            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (((X6) = (X3))
% 0.20/0.51          | ((k4_mcart_1 @ X1 @ X5 @ X6 @ X7)
% 0.20/0.51              != (k4_mcart_1 @ X0 @ X2 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk3' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X6))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((('#_fresh_sk3' @ sk_E)
% 0.20/0.51         = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('sup+', [status(thm)], ['41', '43'])).
% 0.20/0.51  thf('45', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X1 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (('#_fresh_sk3' @ (k4_mcart_1 @ X1 @ X5 @ X6 @ X7)) = (X6))),
% 0.20/0.51      inference('inj_rec', [status(thm)], ['42'])).
% 0.20/0.51  thf('47', plain, ((('#_fresh_sk3' @ sk_E) = (sk_H))),
% 0.20/0.51      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((sk_H) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.20/0.51         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((((sk_H) != (sk_H)))
% 0.20/0.51         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))) | 
% 0.20/0.51       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.20/0.51       ~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.20/0.51       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['29', '40', '51', '52'])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['18', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
