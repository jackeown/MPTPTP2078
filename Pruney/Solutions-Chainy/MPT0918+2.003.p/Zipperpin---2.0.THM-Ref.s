%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.87WY5zgAUK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 157 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          : 1120 (5134 expanded)
%              Number of equality atoms :  185 ( 804 expanded)
%              Maximal formula depth    :   28 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

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

thf('1',plain,
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

thf('2',plain,(
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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X13 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_I )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_I )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X11 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_G )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('26',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,
    ( ( sk_G != sk_G )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_G ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X10 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,
    ( ( sk_F != sk_F )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_F ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15 ) )
      | ( ( k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
        = X12 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( sk_E
    = ( k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = sk_H )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = sk_H )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference(split,[status(esa)],['11'])).

thf('59',plain,
    ( ( sk_H != sk_H )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = sk_H ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_I )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_H )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_F )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('62',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_I ),
    inference('sat_resolution*',[status(thm)],['28','44','60','61'])).

thf('63',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != sk_I ),
    inference(simpl_trail,[status(thm)],['12','62'])).

thf('64',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10','63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.87WY5zgAUK
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 50 iterations in 0.033s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.48  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.48  thf(sk_I_type, type, sk_I: $i).
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
% 0.21/0.48  thf('1', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t59_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ?[E:$i]:
% 0.21/0.48            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.48                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.48                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.48                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.48                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.48                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.21/0.48              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X14 : $i, X15 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.21/0.48          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X13))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((X15) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X15 : $i]:
% 0.21/0.48         (((X15) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.48               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.21/0.48              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X13))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_I))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('5', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_I))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.48  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G))
% 0.21/0.48        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H))
% 0.21/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I)))
% 0.21/0.48         <= (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X14 : $i, X15 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.21/0.48          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X11))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((X15) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X15 : $i]:
% 0.21/0.48         (((X15) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.48               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.21/0.48              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X11))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_G))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.48  thf('18', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_G))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.48  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['20', '21', '22', '23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_G)))
% 0.21/0.48         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_G) != (sk_G)))
% 0.21/0.48         <= (~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X14 : $i, X15 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.21/0.48          | ((k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((X15) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X15 : $i]:
% 0.21/0.48         (((X15) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.48               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((k8_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.21/0.48              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X10))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_F))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.48  thf('34', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_F))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((((sk_D) = (k1_xboole_0))
% 0.21/0.48        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))
% 0.21/0.48        | ((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.48  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)],
% 0.21/0.48                ['36', '37', '38', '39', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_F)))
% 0.21/0.48         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((((sk_F) != (sk_F)))
% 0.21/0.48         <= (~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('46', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X14 : $i, X15 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X14) != (k4_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.21/0.48          | ((k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ X14) = (X12))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((X15) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.48         X15 : $i]:
% 0.21/0.48         (((X15) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k4_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.48               (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X15))
% 0.21/0.48          | ((k10_mcart_1 @ X7 @ X8 @ X9 @ X15 @ 
% 0.21/0.48              (k4_mcart_1 @ X10 @ X11 @ X12 @ X13)) = (X12))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I)) = (sk_H))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.48  thf('50', plain, (((sk_E) = (k4_mcart_1 @ sk_F @ sk_G @ sk_H @ sk_I))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (sk_H))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((sk_D) = (k1_xboole_0))
% 0.21/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '51'])).
% 0.21/0.49  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['52', '53', '54', '55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('split', [status(esa)], ['11'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((((sk_H) != (sk_H)))
% 0.21/0.49         <= (~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I))) | 
% 0.21/0.49       ~ (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_H))) | 
% 0.21/0.49       ~ (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_F))) | 
% 0.21/0.49       ~ (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_G)))),
% 0.21/0.49      inference('split', [status(esa)], ['11'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (~ (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (sk_I)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['28', '44', '60', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (sk_I))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['12', '62'])).
% 0.21/0.49  thf('64', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['7', '8', '9', '10', '63', '64'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
