%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5kNCdnmUw

% Computer   : n005.cluster.edu
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
%              Number of equality atoms :  154 ( 729 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','7','10','11'])).

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
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('22',plain,(
    ! [X19: $i,X21: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_I ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('27',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

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
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['18'])).

thf('34',plain,
    ( ( ( k2_mcart_1 @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_I != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_I ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('40',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

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
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['18'])).

thf('47',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_mcart_1 @ ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('50',plain,(
    ! [X19: $i,X21: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('56',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ sk_F @ sk_G @ sk_H ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('59',plain,(
    ! [X19: $i,X21: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('60',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['18'])).

thf('67',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['18'])).

thf('70',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_F ),
    inference('sat_resolution*',[status(thm)],['36','53','68','69'])).

thf('71',plain,(
    ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_F ),
    inference(simpl_trail,[status(thm)],['19','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5kNCdnmUw
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 57 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_I_type, type, sk_I: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
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
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (((X14) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((k8_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17)
% 0.21/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X17))))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.21/0.49          | ((X18) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d4_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.49       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.49           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.49  thf(t7_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf(d3_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '7', '10', '11'])).
% 0.21/0.49  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['12', '13', '14', '15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.21/0.49         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('20', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.49           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X19 : $i, X21 : $i]: ((k2_mcart_1 @ (k4_tarski @ X19 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, (((k2_mcart_1 @ sk_E) = (sk_I))),
% 0.21/0.49      inference('sup+', [status(thm)], ['20', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (((X14) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((k11_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17) = (k2_mcart_1 @ X17))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.21/0.49          | ((X18) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ sk_E))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['27', '28', '29', '30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_E) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((sk_I) != (sk_I)))
% 0.21/0.49         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('37', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (((X14) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((k10_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17)
% 0.21/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X17)))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.21/0.49          | ((X18) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['40', '41', '42', '43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E)) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      ((((k2_mcart_1 @ (k3_mcart_1 @ sk_F @ sk_G @ sk_H)) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X19 : $i, X21 : $i]: ((k2_mcart_1 @ (k4_tarski @ X19 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((sk_H) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (((X14) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((k9_mcart_1 @ X14 @ X15 @ X16 @ X18 @ X17)
% 0.21/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X17))))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.21/0.49          | ((X18) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, (((k1_mcart_1 @ sk_E) = (k3_mcart_1 @ sk_F @ sk_G @ sk_H))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X19 : $i, X21 : $i]: ((k2_mcart_1 @ (k4_tarski @ X19 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.21/0.49  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['60', '61', '62', '63', '64'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((((sk_G) != (sk_G)))
% 0.21/0.49         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.21/0.49       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))) | 
% 0.21/0.49       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.21/0.49       ~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['36', '53', '68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['19', '70'])).
% 0.21/0.49  thf('72', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['17', '71'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
