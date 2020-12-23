%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5s2nisIdJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 330 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          : 1144 (9998 expanded)
%              Number of equality atoms :  161 (1417 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t82_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = J ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = J ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X9 @ X10 @ X11 @ X13 @ X12 )
        = ( k2_mcart_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ sk_F_1 ) )
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
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7
        = ( k4_mcart_1 @ ( sk_F @ X7 @ X8 @ X6 @ X5 @ X4 ) @ ( sk_G @ X7 @ X8 @ X6 @ X5 @ X4 ) @ ( sk_H @ X7 @ X8 @ X6 @ X5 @ X4 ) @ ( sk_I @ X7 @ X8 @ X6 @ X5 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('11',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14','15'])).

thf('17',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14','15'])).

thf('18',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X7 @ X8 @ X6 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('20',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('25',plain,(
    m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X24 @ sk_D )
      | ( sk_E = X24 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X25 @ X23 @ X26 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X7 @ X8 @ X6 @ X5 @ X4 ) @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('31',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X7 @ X8 @ X6 @ X5 @ X4 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('39',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X7 @ X8 @ X6 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('52',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','36','44','52'])).

thf('54',plain,
    ( sk_E
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['16','54'])).

thf(t78_mcart_1,axiom,(
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

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k4_zfmisc_1 @ X17 @ X16 @ X15 @ X14 ) )
      | ( ( k11_mcart_1 @ X17 @ X16 @ X15 @ X14 @ X18 )
        = X19 )
      | ( X18
       != ( k4_mcart_1 @ X20 @ X21 @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k11_mcart_1 @ X17 @ X16 @ X15 @ X14 @ ( k4_mcart_1 @ X20 @ X21 @ X22 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X20 @ X21 @ X22 @ X19 ) @ ( k4_zfmisc_1 @ X17 @ X16 @ X15 @ X14 ) )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['16','54'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','60'])).

thf('62',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = sk_E ),
    inference('simplify_reflect-',[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = sk_E ),
    inference('sup+',[status(thm)],['7','66'])).

thf('68',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('70',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5s2nisIdJ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 33 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(t82_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( ( ![G:$i]:
% 0.20/0.47           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.47             ( ![H:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.47                 ( ![I:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.47                     ( ![J:$i]:
% 0.20/0.47                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.47                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.47                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47          ( ( ![G:$i]:
% 0.20/0.47              ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.47                ( ![H:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.47                    ( ![I:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.47                        ( ![J:$i]:
% 0.20/0.47                          ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.47                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.47                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t61_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ![E:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.48                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.48                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.48                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.48                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (((X9) = (k1_xboole_0))
% 0.20/0.48          | ((X10) = (k1_xboole_0))
% 0.20/0.48          | ((X11) = (k1_xboole_0))
% 0.20/0.48          | ((k11_mcart_1 @ X9 @ X10 @ X11 @ X13 @ X12) = (k2_mcart_1 @ X12))
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13))
% 0.20/0.48          | ((X13) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.48            = (k2_mcart_1 @ sk_F_1))
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.48         = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l68_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ?[E:$i]:
% 0.20/0.48            ( ( ![F:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.48                  ( ![G:$i]:
% 0.20/0.48                    ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.48                      ( ![H:$i]:
% 0.20/0.48                        ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.48                          ( ![I:$i]:
% 0.20/0.48                            ( ( m1_subset_1 @ I @ D ) =>
% 0.20/0.48                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.20/0.48              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((X4) = (k1_xboole_0))
% 0.20/0.48          | ((X5) = (k1_xboole_0))
% 0.20/0.48          | ((X6) = (k1_xboole_0))
% 0.20/0.48          | ((X7)
% 0.20/0.48              = (k4_mcart_1 @ (sk_F @ X7 @ X8 @ X6 @ X5 @ X4) @ 
% 0.20/0.48                 (sk_G @ X7 @ X8 @ X6 @ X5 @ X4) @ 
% 0.20/0.48                 (sk_H @ X7 @ X8 @ X6 @ X5 @ X4) @ 
% 0.20/0.48                 (sk_I @ X7 @ X8 @ X6 @ X5 @ X4)))
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8))
% 0.20/0.48          | ((X8) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | ((sk_F_1)
% 0.20/0.48            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((sk_F_1)
% 0.20/0.48         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['11', '12', '13', '14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((sk_F_1)
% 0.20/0.48         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['11', '12', '13', '14', '15'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((X4) = (k1_xboole_0))
% 0.20/0.48          | ((X5) = (k1_xboole_0))
% 0.20/0.48          | ((X6) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_G @ X7 @ X8 @ X6 @ X5 @ X4) @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8))
% 0.20/0.48          | ((X8) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['20', '21', '22', '23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X23 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X24 @ sk_D)
% 0.20/0.48          | ((sk_E) = (X24))
% 0.20/0.48          | ((sk_F_1) != (k4_mcart_1 @ X25 @ X23 @ X26 @ X24))
% 0.20/0.48          | ~ (m1_subset_1 @ X26 @ sk_C)
% 0.20/0.48          | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.48          | ((sk_F_1)
% 0.20/0.48              != (k4_mcart_1 @ X0 @ 
% 0.20/0.48                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.20/0.48          | ((sk_E) = (X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((sk_F_1) != (sk_F_1))
% 0.20/0.48        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.48        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.48        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((X4) = (k1_xboole_0))
% 0.20/0.48          | ((X5) = (k1_xboole_0))
% 0.20/0.48          | ((X6) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_I @ X7 @ X8 @ X6 @ X5 @ X4) @ X8)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8))
% 0.20/0.48          | ((X8) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['31', '32', '33', '34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((X4) = (k1_xboole_0))
% 0.20/0.48          | ((X5) = (k1_xboole_0))
% 0.20/0.48          | ((X6) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_H @ X7 @ X8 @ X6 @ X5 @ X4) @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8))
% 0.20/0.48          | ((X8) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['39', '40', '41', '42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((X4) = (k1_xboole_0))
% 0.20/0.48          | ((X5) = (k1_xboole_0))
% 0.20/0.48          | ((X6) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_F @ X7 @ X8 @ X6 @ X5 @ X4) @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k4_zfmisc_1 @ X4 @ X5 @ X6 @ X8))
% 0.20/0.48          | ((X8) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((sk_D) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['47', '48', '49', '50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((((sk_F_1) != (sk_F_1))
% 0.20/0.48        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '36', '44', '52'])).
% 0.20/0.48  thf('54', plain, (((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((sk_F_1)
% 0.20/0.48         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '54'])).
% 0.20/0.48  thf(t78_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.48              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.48                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.48                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.48                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.48                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.20/0.48         X21 : $i, X22 : $i]:
% 0.20/0.48         (((X14) = (k1_xboole_0))
% 0.20/0.48          | ((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((X17) = (k1_xboole_0))
% 0.20/0.48          | ~ (m1_subset_1 @ X18 @ (k4_zfmisc_1 @ X17 @ X16 @ X15 @ X14))
% 0.20/0.48          | ((k11_mcart_1 @ X17 @ X16 @ X15 @ X14 @ X18) = (X19))
% 0.20/0.48          | ((X18) != (k4_mcart_1 @ X20 @ X21 @ X22 @ X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.20/0.48         X22 : $i]:
% 0.20/0.48         (((k11_mcart_1 @ X17 @ X16 @ X15 @ X14 @ 
% 0.20/0.48            (k4_mcart_1 @ X20 @ X21 @ X22 @ X19)) = (X19))
% 0.20/0.48          | ~ (m1_subset_1 @ (k4_mcart_1 @ X20 @ X21 @ X22 @ X19) @ 
% 0.20/0.48               (k4_zfmisc_1 @ X17 @ X16 @ X15 @ X14))
% 0.20/0.48          | ((X17) = (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X14) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((X2) = (k1_xboole_0))
% 0.20/0.48          | ((X3) = (k1_xboole_0))
% 0.20/0.48          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.48              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.20/0.48              = (sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (((sk_F_1)
% 0.20/0.48         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '54'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((X2) = (k1_xboole_0))
% 0.20/0.48          | ((X3) = (k1_xboole_0))
% 0.20/0.48          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E)))),
% 0.20/0.48      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '60'])).
% 0.20/0.48  thf('62', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)],
% 0.20/0.48                ['61', '62', '63', '64', '65'])).
% 0.20/0.48  thf('67', plain, (((k2_mcart_1 @ sk_F_1) = (sk_E))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.48         = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.48  thf('70', plain, (((sk_E) != (k2_mcart_1 @ sk_F_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['67', '70'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
