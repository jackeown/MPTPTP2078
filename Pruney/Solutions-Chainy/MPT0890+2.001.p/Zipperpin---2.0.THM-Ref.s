%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l287lbEHDf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 (1154 expanded)
%              Number of leaves         :   24 ( 367 expanded)
%              Depth                    :   21
%              Number of atoms          : 1367 (23957 expanded)
%              Number of equality atoms :  180 (3221 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                    = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                  & ( ( k6_mcart_1 @ A @ B @ C @ D )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                  & ( ( k7_mcart_1 @ A @ B @ C @ D )
                    = ( k2_mcart_1 @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l44_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ! [G: $i] :
                        ( ( m1_subset_1 @ G @ C )
                       => ( D
                         != ( k3_mcart_1 @ E @ F @ G ) ) ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

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
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('14',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('27',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('28',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t47_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ? [E: $i,F: $i,G: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                      = E )
                    & ( ( k6_mcart_1 @ A @ B @ C @ D )
                      = F )
                    & ( ( k7_mcart_1 @ A @ B @ C @ D )
                      = G ) )
                & ( D
                  = ( k3_mcart_1 @ E @ F @ G ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X15
       != ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
      | ( ( k5_mcart_1 @ X10 @ X11 @ X16 @ X15 )
        = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( ( k5_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X12 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X16 ) )
      | ( ( k5_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X12 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('47',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X15
       != ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X16 @ X15 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X14 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X16 ) )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X14 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) )
        = ( k2_mcart_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( k2_mcart_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['44'])).

thf('61',plain,
    ( ( ( k2_mcart_1 @ sk_D )
     != ( k2_mcart_1 @ sk_D ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('64',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X15
       != ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X16 @ X15 )
        = X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X13 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X16 ) )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X13 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('78',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['44'])).

thf('81',plain,(
    ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['62','79','80'])).

thf('82',plain,(
    ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['45','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l287lbEHDf
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 57 iterations in 0.043s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(t50_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ~( ![D:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51             ( ~( ![D:$i]:
% 0.21/0.51                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                    ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                        ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                      ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                        ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                      ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t50_mcart_1])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(l44_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ?[D:$i]:
% 0.21/0.51            ( ( ![E:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.51                  ( ![F:$i]:
% 0.21/0.51                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.51                      ( ![G:$i]:
% 0.21/0.51                        ( ( m1_subset_1 @ G @ C ) =>
% 0.21/0.51                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.21/0.51              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (((X6) = (k1_xboole_0))
% 0.21/0.51          | ((X7) = (k1_xboole_0))
% 0.21/0.51          | ((X8)
% 0.21/0.51              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.21/0.51                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.51          | ((X9) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (((X6) = (k1_xboole_0))
% 0.21/0.51          | ((X7) = (k1_xboole_0))
% 0.21/0.51          | ((X8)
% 0.21/0.51              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.21/0.51                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.51          | ((X9) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0))
% 0.21/0.51        | ((sk_D)
% 0.21/0.51            = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51               (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51               (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.51  thf(d3_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf(t7_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((k2_mcart_1 @ sk_D) = (sk_G @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.52           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((k1_mcart_1 @ sk_D)
% 0.21/0.52         = (k4_tarski @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((k1_mcart_1 @ (k1_mcart_1 @ sk_D)) = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((k1_mcart_1 @ sk_D)
% 0.21/0.52         = (k4_tarski @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((k1_mcart_1 @ (k1_mcart_1 @ sk_D)) = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((k1_mcart_1 @ sk_D)
% 0.21/0.52         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((k2_mcart_1 @ (k1_mcart_1 @ sk_D)) = (sk_F @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf(t47_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ?[D:$i]:
% 0.21/0.52            ( ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.52                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.52                       ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.52                       ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.52                  ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) & 
% 0.21/0.52              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (((X10) = (k1_xboole_0))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X15) != (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52          | ((k5_mcart_1 @ X10 @ X11 @ X16 @ X15) = (X12))
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((X16) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((k5_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X12))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X16))
% 0.21/0.52          | ((k5_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X12))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.52              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.21/0.52              = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D)
% 0.21/0.52              = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '38'])).
% 0.21/0.52  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          != (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52            != (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          != (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52                = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.21/0.52      inference('split', [status(esa)], ['44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (((X10) = (k1_xboole_0))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X15) != (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52          | ((k7_mcart_1 @ X10 @ X11 @ X16 @ X15) = (X14))
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((X16) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((k7_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X14))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X16))
% 0.21/0.52          | ((k7_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X14))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.52              (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52               (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))
% 0.21/0.52              = (k2_mcart_1 @ sk_D))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.52            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '54'])).
% 0.21/0.52  thf('56', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('58', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k2_mcart_1 @ sk_D)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))))),
% 0.21/0.52      inference('split', [status(esa)], ['44'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((((k2_mcart_1 @ sk_D) != (k2_mcart_1 @ sk_D)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (((X10) = (k1_xboole_0))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X15) != (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ X15) = (X13))
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((X16) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.52          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X13))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (((X16) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X16))
% 0.21/0.52          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.52              = (X13))
% 0.21/0.52          | ((X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.52              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.21/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.52            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D)
% 0.21/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['63', '71'])).
% 0.21/0.52  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('75', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['72', '73', '74', '75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          != (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52                = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.21/0.52      inference('split', [status(esa)], ['44'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.21/0.52          != (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52                = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))) | 
% 0.21/0.52       ~
% 0.21/0.52       (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))) | 
% 0.21/0.52       ~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['44'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52          = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['62', '79', '80'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.52         != (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['45', '81'])).
% 0.21/0.52  thf('83', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['43', '82'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
