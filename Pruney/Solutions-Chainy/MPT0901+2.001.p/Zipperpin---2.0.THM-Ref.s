%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2IMqsNpRTB

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  193 (26697 expanded)
%              Number of leaves         :   27 (8314 expanded)
%              Depth                    :   28
%              Number of atoms          : 3048 (803919 expanded)
%              Number of equality atoms :  362 (101298 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t61_mcart_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
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
                    = ( k2_mcart_1 @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l68_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ? [E: $i] :
            ( ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ B )
                   => ! [H: $i] :
                        ( ( m1_subset_1 @ H @ C )
                       => ! [I: $i] :
                            ( ( m1_subset_1 @ I @ D )
                           => ( E
                             != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )
            & ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14
        = ( k4_mcart_1 @ ( sk_F @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_G @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_H @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_I @ X14 @ X15 @ X13 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('3',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6','7'])).

thf('9',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6','7'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('10',plain,(
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

thf('11',plain,(
    ! [X25: $i,X27: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X25 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_E )
    = ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('21',plain,(
    ! [X25: $i,X27: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X25 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('26',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('27',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('36',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i,X27: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X25 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','33','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k4_tarski @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ sk_E ) @ X0 )
      = ( k4_tarski @ sk_E @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('45',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('46',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('50',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('51',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('53',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('55',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) @ X0 )
      = ( k4_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['43','48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ sk_E @ X0 ) )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('60',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

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

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X23
       != ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
      | ( ( k11_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k11_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X22 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 ) )
        = X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) )
        = X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) )
        = X0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
        = X0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
        = ( k2_mcart_1 @ sk_E ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','78'])).

thf('80',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( k2_mcart_1 @ sk_E ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X23
       != ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
      | ( ( k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23 )
        = X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X20 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('110',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('116',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X23
       != ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
      | ( ( k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23 )
        = X19 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('117',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X19 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','123'])).

thf('125',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','126'])).

thf('128',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['127','128','129','130','131'])).

thf('133',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('134',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('140',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X23
       != ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
      | ( ( k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23 )
        = X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('141',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X21 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 ) )
        = X1 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2 ) )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X5 @ X4 @ X3 @ X2 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 @ X0 ) )
        = X1 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X4 @ X3 @ X2 @ X1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','147'])).

thf('149',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','150'])).

thf('152',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('158',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('161',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_mcart_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['111','135','159','160'])).

thf('162',plain,(
    ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_mcart_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['87','161'])).

thf('163',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','83','84','85','162','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2IMqsNpRTB
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:21:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 157 iterations in 0.084s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.53  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.53  thf(t61_mcart_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ~( ![E:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.19/0.53                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.19/0.53                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.19/0.53                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.19/0.53                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53             ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53             ( ~( ![E:$i]:
% 0.19/0.53                  ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.19/0.53                    ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                        ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.19/0.53                      ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                        ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.19/0.53                      ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                        ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.19/0.53                      ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.53                        ( k2_mcart_1 @ E ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t61_mcart_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(l68_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ?[E:$i]:
% 0.19/0.53            ( ( ![F:$i]:
% 0.19/0.53                ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.53                  ( ![G:$i]:
% 0.19/0.53                    ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.53                      ( ![H:$i]:
% 0.19/0.53                        ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.53                          ( ![I:$i]:
% 0.19/0.53                            ( ( m1_subset_1 @ I @ D ) =>
% 0.19/0.53                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.19/0.53              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.53         (((X11) = (k1_xboole_0))
% 0.19/0.53          | ((X12) = (k1_xboole_0))
% 0.19/0.53          | ((X13) = (k1_xboole_0))
% 0.19/0.53          | ((X14)
% 0.19/0.53              = (k4_mcart_1 @ (sk_F @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.19/0.53                 (sk_G @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.19/0.53                 (sk_H @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.19/0.53                 (sk_I @ X14 @ X15 @ X13 @ X12 @ X11)))
% 0.19/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.19/0.53          | ((X15) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      ((((sk_D) = (k1_xboole_0))
% 0.19/0.53        | ((sk_E)
% 0.19/0.53            = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53               (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53               (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.19/0.53        | ((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('7', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.19/0.53  thf(d4_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.53       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.53           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.19/0.53  thf(t7_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X25 : $i, X27 : $i]: ((k2_mcart_1 @ (k4_tarski @ X25 @ X27)) = (X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (((k2_mcart_1 @ sk_E) = (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['9', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['8', '13'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['8', '13'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.53           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['15', '18'])).
% 0.19/0.53  thf(d3_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X25 : $i, X27 : $i]: ((k2_mcart_1 @ (k4_tarski @ X25 @ X27)) = (X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['14', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['15', '18'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '22'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['27', '30'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['27', '30'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      (![X25 : $i, X27 : $i]: ((k2_mcart_1 @ (k4_tarski @ X25 @ X27)) = (X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((sk_E)
% 0.19/0.53         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['24', '33', '38'])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.53           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k3_mcart_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 0.19/0.53           = (k4_tarski @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.19/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ 
% 0.19/0.53           (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ sk_E) @ X0) = (k4_tarski @ sk_E @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['39', '42'])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53         = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E) @ X0)
% 0.19/0.53           = (k4_tarski @ sk_E @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['43', '48', '55'])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k1_mcart_1 @ (k4_tarski @ sk_E @ X0))
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['56', '57'])).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      (((k1_mcart_1 @ sk_E)
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('63', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.53  thf('65', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('67', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.19/0.53           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.19/0.53      inference('sup+', [status(thm)], ['65', '66'])).
% 0.19/0.53  thf('68', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.53           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.19/0.53  thf('69', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['67', '68'])).
% 0.19/0.53  thf('70', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf(t59_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ?[E:$i]:
% 0.19/0.53            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.19/0.53                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.19/0.53                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.19/0.53                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.19/0.53                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.19/0.53                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.19/0.53              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.19/0.53  thf('71', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X23 : $i, X24 : $i]:
% 0.19/0.53         (((X16) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.19/0.53          | ((k11_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X22))
% 0.19/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((X24) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.19/0.53  thf('72', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X24 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.19/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((k11_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.19/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X22))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X16) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['71'])).
% 0.19/0.53  thf('73', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k4_mcart_1 @ 
% 0.19/0.53               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0))
% 0.19/0.53              = (X0))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['70', '72'])).
% 0.19/0.53  thf('74', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))
% 0.19/0.53              = (X0))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.19/0.53  thf('76', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))
% 0.19/0.53              = (X0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['63', '75'])).
% 0.19/0.53  thf('77', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('78', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)) = (X0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.53  thf('79', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.19/0.53              = (k2_mcart_1 @ sk_E))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['60', '78'])).
% 0.19/0.53  thf('80', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('81', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.53  thf('82', plain,
% 0.19/0.53      ((((sk_D) = (k1_xboole_0))
% 0.19/0.53        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            = (k2_mcart_1 @ sk_E))
% 0.19/0.53        | ((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '81'])).
% 0.19/0.53  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('85', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('86', plain,
% 0.19/0.53      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            != (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('87', plain,
% 0.19/0.53      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          != (k2_mcart_1 @ sk_E)))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k2_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('split', [status(esa)], ['86'])).
% 0.19/0.53  thf('88', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('89', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('90', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('91', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('92', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X23 : $i, X24 : $i]:
% 0.19/0.53         (((X16) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.19/0.53          | ((k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X20))
% 0.19/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((X24) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.19/0.53  thf('93', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X24 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.19/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.19/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X20))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X16) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['92'])).
% 0.19/0.53  thf('94', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k4_mcart_1 @ 
% 0.19/0.53               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['91', '93'])).
% 0.19/0.53  thf('95', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('96', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.19/0.53  thf('97', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['90', '96'])).
% 0.19/0.53  thf('98', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('99', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['97', '98'])).
% 0.19/0.53  thf('100', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['89', '99'])).
% 0.19/0.53  thf('101', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('102', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.19/0.53  thf('103', plain,
% 0.19/0.53      ((((sk_D) = (k1_xboole_0))
% 0.19/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53        | ((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['88', '102'])).
% 0.19/0.53  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('105', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('106', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('107', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('108', plain,
% 0.19/0.53      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)],
% 0.19/0.53                ['103', '104', '105', '106', '107'])).
% 0.19/0.53  thf('109', plain,
% 0.19/0.53      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.19/0.53      inference('split', [status(esa)], ['86'])).
% 0.19/0.53  thf('110', plain,
% 0.19/0.53      ((((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['108', '109'])).
% 0.19/0.53  thf('111', plain,
% 0.19/0.53      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('simplify', [status(thm)], ['110'])).
% 0.19/0.53  thf('112', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('113', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('114', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('115', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('116', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X23 : $i, X24 : $i]:
% 0.19/0.53         (((X16) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.19/0.53          | ((k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X19))
% 0.19/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((X24) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.19/0.53  thf('117', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X24 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.19/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.19/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X19))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X16) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['116'])).
% 0.19/0.53  thf('118', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k4_mcart_1 @ 
% 0.19/0.53               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0))
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['115', '117'])).
% 0.19/0.53  thf('119', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('120', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['118', '119'])).
% 0.19/0.53  thf('121', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['114', '120'])).
% 0.19/0.53  thf('122', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('123', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['121', '122'])).
% 0.19/0.53  thf('124', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['113', '123'])).
% 0.19/0.53  thf('125', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('126', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['124', '125'])).
% 0.19/0.53  thf('127', plain,
% 0.19/0.53      ((((sk_D) = (k1_xboole_0))
% 0.19/0.53        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53        | ((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['112', '126'])).
% 0.19/0.53  thf('128', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('129', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('130', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('131', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('132', plain,
% 0.19/0.53      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)],
% 0.19/0.53                ['127', '128', '129', '130', '131'])).
% 0.19/0.53  thf('133', plain,
% 0.19/0.53      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.19/0.53      inference('split', [status(esa)], ['86'])).
% 0.19/0.53  thf('134', plain,
% 0.19/0.53      ((((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['132', '133'])).
% 0.19/0.53  thf('135', plain,
% 0.19/0.53      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('simplify', [status(thm)], ['134'])).
% 0.19/0.53  thf('136', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('137', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('138', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('139', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('140', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X23 : $i, X24 : $i]:
% 0.19/0.53         (((X16) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.19/0.53          | ((k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X21))
% 0.19/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((X24) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.19/0.53  thf('141', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.19/0.53         X24 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.19/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.19/0.53          | ((k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.19/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X21))
% 0.19/0.53          | ((X18) = (k1_xboole_0))
% 0.19/0.53          | ((X17) = (k1_xboole_0))
% 0.19/0.53          | ((X16) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['140'])).
% 0.19/0.53  thf('142', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k4_mcart_1 @ 
% 0.19/0.53               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0))
% 0.19/0.53              = (X1))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['139', '141'])).
% 0.19/0.53  thf('143', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ X1 @ X0)
% 0.19/0.53           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['64', '69'])).
% 0.19/0.53  thf('144', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ 
% 0.19/0.53             (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X5 @ X4 @ X3 @ X2))
% 0.19/0.53          | ((X5) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X5 @ X4 @ X3 @ X2 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1 @ X0))
% 0.19/0.53              = (X1))
% 0.19/0.53          | ((X2) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['142', '143'])).
% 0.19/0.53  thf('145', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['138', '144'])).
% 0.19/0.53  thf('146', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.19/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.19/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('147', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0) @ 
% 0.19/0.53             (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X4 @ X3 @ X2 @ X1 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X4) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['145', '146'])).
% 0.19/0.53  thf('148', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.19/0.53              (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['137', '147'])).
% 0.19/0.53  thf('149', plain,
% 0.19/0.53      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.53  thf('150', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.53          | ((X3) = (k1_xboole_0))
% 0.19/0.53          | ((X2) = (k1_xboole_0))
% 0.19/0.53          | ((X1) = (k1_xboole_0))
% 0.19/0.53          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53          | ((X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['148', '149'])).
% 0.19/0.53  thf('151', plain,
% 0.19/0.53      ((((sk_D) = (k1_xboole_0))
% 0.19/0.53        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.53        | ((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['136', '150'])).
% 0.19/0.53  thf('152', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('153', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('154', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('155', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('156', plain,
% 0.19/0.53      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)],
% 0.19/0.53                ['151', '152', '153', '154', '155'])).
% 0.19/0.53  thf('157', plain,
% 0.19/0.53      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          != (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('split', [status(esa)], ['86'])).
% 0.19/0.53  thf('158', plain,
% 0.19/0.53      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.19/0.53          != (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.19/0.53         <= (~
% 0.19/0.53             (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53                = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['156', '157'])).
% 0.19/0.53  thf('159', plain,
% 0.19/0.53      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.53      inference('simplify', [status(thm)], ['158'])).
% 0.19/0.53  thf('160', plain,
% 0.19/0.53      (~
% 0.19/0.53       (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E))) | 
% 0.19/0.53       ~
% 0.19/0.53       (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))) | 
% 0.19/0.53       ~
% 0.19/0.53       (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))) | 
% 0.19/0.53       ~
% 0.19/0.53       (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.53          = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.19/0.53      inference('split', [status(esa)], ['86'])).
% 0.19/0.53  thf('161', plain,
% 0.19/0.53      (~
% 0.19/0.53       (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E)))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['111', '135', '159', '160'])).
% 0.19/0.53  thf('162', plain,
% 0.19/0.53      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) != (k2_mcart_1 @ sk_E))),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['87', '161'])).
% 0.19/0.53  thf('163', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('164', plain, ($false),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)],
% 0.19/0.53                ['82', '83', '84', '85', '162', '163'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
