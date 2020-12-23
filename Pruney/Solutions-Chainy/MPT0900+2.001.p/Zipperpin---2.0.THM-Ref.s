%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.snS21iWVnn

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 (2480 expanded)
%              Number of leaves         :   20 ( 744 expanded)
%              Depth                    :   25
%              Number of atoms          : 1527 (81429 expanded)
%              Number of equality atoms :  176 (9321 expanded)
%              Maximal formula depth    :   27 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(t60_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ~ ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
               => ( E
                  = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_mcart_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3
        = ( k4_mcart_1 @ ( sk_F @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_G @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_H @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_I @ X3 @ X4 @ X2 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
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
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

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
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X12
       != ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
      | ( ( k8_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12 )
        = X8 )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( ( k8_mcart_1 @ X5 @ X6 @ X7 @ X13 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
        = X8 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
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
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X12
       != ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
      | ( ( k9_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12 )
        = X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( ( k9_mcart_1 @ X5 @ X6 @ X7 @ X13 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
        = X9 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X12
       != ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
      | ( ( k10_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12 )
        = X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( ( k10_mcart_1 @ X5 @ X6 @ X7 @ X13 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
        = X10 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X12
       != ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
      | ( ( k11_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12 )
        = X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13 ) )
      | ( ( k11_mcart_1 @ X5 @ X6 @ X7 @ X13 @ ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 ) )
        = X11 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E )
        = ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['49','62'])).

thf('64',plain,(
    sk_E
 != ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.snS21iWVnn
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 42 iterations in 0.031s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(t60_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ~( ![E:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.49                 ( ( E ) =
% 0.20/0.49                   ( k4_mcart_1 @
% 0.20/0.49                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ~( ![E:$i]:
% 0.20/0.49                  ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.49                    ( ( E ) =
% 0.20/0.49                      ( k4_mcart_1 @
% 0.20/0.49                        ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                        ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                        ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                        ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t60_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l68_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ?[E:$i]:
% 0.20/0.49            ( ( ![F:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.49                  ( ![G:$i]:
% 0.20/0.49                    ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.49                      ( ![H:$i]:
% 0.20/0.49                        ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.49                          ( ![I:$i]:
% 0.20/0.49                            ( ( m1_subset_1 @ I @ D ) =>
% 0.20/0.49                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.20/0.49              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X3)
% 0.20/0.49              = (k4_mcart_1 @ (sk_F @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.20/0.49                 (sk_G @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.20/0.49                 (sk_H @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.20/0.49                 (sk_I @ X3 @ X4 @ X2 @ X1 @ X0)))
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.20/0.49          | ((X4) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((((sk_D) = (k1_xboole_0))
% 0.20/0.49        | ((sk_E)
% 0.20/0.49            = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.49  thf(t59_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ?[E:$i]:
% 0.20/0.49            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.49                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.49                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.49                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.49                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.49                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.20/0.49              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X12 : $i, X13 : $i]:
% 0.20/0.49         (((X5) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X12) != (k4_mcart_1 @ X8 @ X9 @ X10 @ X11))
% 0.20/0.49          | ((k8_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12) = (X8))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((X13) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X13 : $i]:
% 0.20/0.49         (((X13) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.49               (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((k8_mcart_1 @ X5 @ X6 @ X7 @ X13 @ 
% 0.20/0.49              (k4_mcart_1 @ X8 @ X9 @ X10 @ X11)) = (X8))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X5) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.49              (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.49              = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.20/0.49              = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((sk_D) = (k1_xboole_0))
% 0.20/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.49  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (sk_F @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)],
% 0.20/0.49                ['15', '16', '17', '18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '20'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X12 : $i, X13 : $i]:
% 0.20/0.49         (((X5) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X12) != (k4_mcart_1 @ X8 @ X9 @ X10 @ X11))
% 0.20/0.49          | ((k9_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12) = (X9))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((X13) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X13 : $i]:
% 0.20/0.49         (((X13) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.49               (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((k9_mcart_1 @ X5 @ X6 @ X7 @ X13 @ 
% 0.20/0.49              (k4_mcart_1 @ X8 @ X9 @ X10 @ X11)) = (X9))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X5) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.49              (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.49              = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '20'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.20/0.49              = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_D) = (k1_xboole_0))
% 0.20/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '28'])).
% 0.20/0.49  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (sk_G @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)],
% 0.20/0.49                ['29', '30', '31', '32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X12 : $i, X13 : $i]:
% 0.20/0.49         (((X5) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X12) != (k4_mcart_1 @ X8 @ X9 @ X10 @ X11))
% 0.20/0.49          | ((k10_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12) = (X10))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((X13) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X13 : $i]:
% 0.20/0.49         (((X13) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.49               (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((k10_mcart_1 @ X5 @ X6 @ X7 @ X13 @ 
% 0.20/0.49              (k4_mcart_1 @ X8 @ X9 @ X10 @ X11)) = (X10))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X5) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.49              (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.49              = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.20/0.49              = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((((sk_D) = (k1_xboole_0))
% 0.20/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '42'])).
% 0.20/0.49  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (sk_H @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)],
% 0.20/0.49                ['43', '44', '45', '46', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '48'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X12 : $i, X13 : $i]:
% 0.20/0.49         (((X5) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X12) != (k4_mcart_1 @ X8 @ X9 @ X10 @ X11))
% 0.20/0.49          | ((k11_mcart_1 @ X5 @ X6 @ X7 @ X13 @ X12) = (X11))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((X13) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.49         X13 : $i]:
% 0.20/0.49         (((X13) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.49               (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X13))
% 0.20/0.49          | ((k11_mcart_1 @ X5 @ X6 @ X7 @ X13 @ 
% 0.20/0.49              (k4_mcart_1 @ X8 @ X9 @ X10 @ X11)) = (X11))
% 0.20/0.49          | ((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ((X5) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.49              (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.49              = (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '48'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X2) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_E)
% 0.20/0.49              = (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((((sk_D) = (k1_xboole_0))
% 0.20/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.49  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('60', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (sk_I @ sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)],
% 0.20/0.49                ['57', '58', '59', '60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (((sk_E)
% 0.20/0.49         != (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
