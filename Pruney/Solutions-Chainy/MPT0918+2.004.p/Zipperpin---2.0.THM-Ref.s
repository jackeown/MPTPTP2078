%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PFlSoWQqIA

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 310 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          : 1680 (7906 expanded)
%              Number of equality atoms :  257 (1158 expanded)
%              Maximal formula depth    :   28 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('19',plain,
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

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X14
       != ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14 )
        = X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X13 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 @ X15 ) )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X13 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','16'])).

thf('37',plain,
    ( ( ( k2_mcart_1 @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('39',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X14
       != ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14 )
        = X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X11 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 @ X15 ) )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X11 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','46'])).

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
    inference(split,[status(esa)],['34'])).

thf('54',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('57',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X14
       != ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ( ( k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14 )
        = X10 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X10 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X15 ) )
      | ( ( k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X10 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['34'])).

thf('74',plain,
    ( ( sk_F != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('77',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X14
       != ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ( ( k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X12 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('81',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 @ X15 ) )
      | ( ( k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X12 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference('simplify_reflect-',[status(thm)],['85','86','87','88','89'])).

thf('91',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['34'])).

thf('92',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['34'])).

thf('95',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_I ),
    inference('sat_resolution*',[status(thm)],['55','75','93','94'])).

thf('96',plain,(
    ( k2_mcart_1 @ sk_E )
 != sk_I ),
    inference(simpl_trail,[status(thm)],['37','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PFlSoWQqIA
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 77 iterations in 0.048s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.51  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.51  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_H_type, type, sk_H: $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(sk_I_type, type, sk_I: $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(t78_mcart_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.22/0.51              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.22/0.51                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.22/0.51                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.22/0.51                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.22/0.51                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.51        ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.51          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51               ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51               ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.22/0.51                 ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.22/0.51                        ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.22/0.51                        ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.22/0.51                        ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.22/0.51                   ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t78_mcart_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d4_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf(d3_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.22/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.22/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf(t61_mcart_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ~( ![E:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.51                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.51                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.51                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.51                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.51                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.51                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.22/0.51                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         (((X16) = (k1_xboole_0))
% 0.22/0.51          | ((X17) = (k1_xboole_0))
% 0.22/0.51          | ((X18) = (k1_xboole_0))
% 0.22/0.51          | ((k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19) = (k2_mcart_1 @ X19))
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20))
% 0.22/0.51          | ((X20) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.22/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         (((X16) = (k1_xboole_0))
% 0.22/0.51          | ((X17) = (k1_xboole_0))
% 0.22/0.51          | ((X18) = (k1_xboole_0))
% 0.22/0.51          | ((k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19) = (k2_mcart_1 @ X19))
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.22/0.51               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18 @ X20))
% 0.22/0.51          | ((X20) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      ((((sk_D) = (k1_xboole_0))
% 0.22/0.51        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.22/0.51            = (k2_mcart_1 @ sk_E))
% 0.22/0.51        | ((sk_C) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.51  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['12', '13', '14', '15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('19', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t59_mcart_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ?[E:$i]:
% 0.22/0.51            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.22/0.51                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.22/0.51                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.22/0.51                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.22/0.51                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.22/0.51                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.22/0.51              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X14 : $i, X15 : $i]:
% 0.22/0.51         (((X7) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.22/0.51          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X13))
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((X15) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X13))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.22/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9 @ X15))
% 0.22/0.51          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X13))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.22/0.51              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_I))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '23'])).
% 0.22/0.51  thf('25', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_I))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((((sk_D) = (k1_xboole_0))
% 0.22/0.51        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))
% 0.22/0.51        | ((sk_C) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '26'])).
% 0.22/0.51  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['27', '28', '29', '30', '31'])).
% 0.22/0.51  thf('33', plain, (((k2_mcart_1 @ sk_E) = (sk_I))),
% 0.22/0.51      inference('sup+', [status(thm)], ['17', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.22/0.51        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.22/0.51        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.22/0.51        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.22/0.51         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.22/0.51      inference('split', [status(esa)], ['34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['12', '13', '14', '15', '16'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((((k2_mcart_1 @ sk_E) != (sk_I)))
% 0.22/0.51         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.22/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('39', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X14 : $i, X15 : $i]:
% 0.22/0.51         (((X7) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.22/0.51          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X11))
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((X15) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X11))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.22/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9 @ X15))
% 0.22/0.51          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X11))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.22/0.51              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_G))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['39', '43'])).
% 0.22/0.51  thf('45', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_G))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      ((((sk_D) = (k1_xboole_0))
% 0.22/0.51        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.22/0.51        | ((sk_C) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '46'])).
% 0.22/0.51  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['47', '48', '49', '50', '51'])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.22/0.51         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.22/0.51      inference('split', [status(esa)], ['34'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      ((((sk_G) != (sk_G)))
% 0.22/0.51         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('57', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X14 : $i, X15 : $i]:
% 0.22/0.51         (((X7) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.22/0.51          | ((k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X10))
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((X15) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X10))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X15))
% 0.22/0.51          | ((k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X10))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.22/0.51              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_F))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['57', '61'])).
% 0.22/0.51  thf('63', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_F))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('66', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_F))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((((sk_D) = (k1_xboole_0))
% 0.22/0.51        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.22/0.51        | ((sk_C) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['56', '66'])).
% 0.22/0.51  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('70', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('71', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['67', '68', '69', '70', '71'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.22/0.51         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.22/0.51      inference('split', [status(esa)], ['34'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      ((((sk_F) != (sk_F)))
% 0.22/0.51         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.51  thf('75', plain,
% 0.22/0.51      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['74'])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('77', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X14 : $i, X15 : $i]:
% 0.22/0.51         (((X7) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.22/0.51          | ((k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X12))
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((X15) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.22/0.51          | ((k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X12))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.51           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.22/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.22/0.51         X15 : $i]:
% 0.22/0.51         (((X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.22/0.51               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9 @ X15))
% 0.22/0.51          | ((k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.22/0.51              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X12))
% 0.22/0.51          | ((X9) = (k1_xboole_0))
% 0.22/0.51          | ((X8) = (k1_xboole_0))
% 0.22/0.51          | ((X7) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['79', '80'])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.22/0.51              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_H))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['77', '81'])).
% 0.22/0.51  thf('83', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('84', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ sk_E @ 
% 0.22/0.51             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.22/0.51          | ((X3) = (k1_xboole_0))
% 0.22/0.51          | ((X2) = (k1_xboole_0))
% 0.22/0.51          | ((X1) = (k1_xboole_0))
% 0.22/0.51          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_H))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.51  thf('85', plain,
% 0.22/0.51      ((((sk_D) = (k1_xboole_0))
% 0.22/0.51        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))
% 0.22/0.51        | ((sk_C) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['76', '84'])).
% 0.22/0.51  thf('86', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('87', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('88', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('89', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)],
% 0.22/0.51                ['85', '86', '87', '88', '89'])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.22/0.51         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.22/0.51      inference('split', [status(esa)], ['34'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      ((((sk_H) != (sk_H)))
% 0.22/0.52         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['90', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['92'])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))) | 
% 0.22/0.52       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.22/0.52       ~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.22/0.52       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['34'])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['55', '75', '93', '94'])).
% 0.22/0.52  thf('96', plain, (((k2_mcart_1 @ sk_E) != (sk_I))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['37', '95'])).
% 0.22/0.52  thf('97', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['33', '96'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
