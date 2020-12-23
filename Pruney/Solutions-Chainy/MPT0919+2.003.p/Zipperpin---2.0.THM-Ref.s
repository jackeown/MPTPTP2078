%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhOpLa8UXQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 330 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          : 1156 (10014 expanded)
%              Number of equality atoms :  161 (1417 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t79_mcart_1,conjecture,(
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
                         => ( E = G ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = G ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_mcart_1])).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X12 @ X13 @ X14 @ X16 @ X15 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X15 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
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
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10
        = ( k4_mcart_1 @ ( sk_F @ X10 @ X11 @ X9 @ X8 @ X7 ) @ ( sk_G @ X10 @ X11 @ X9 @ X8 @ X7 ) @ ( sk_H @ X10 @ X11 @ X9 @ X8 @ X7 ) @ ( sk_I @ X10 @ X11 @ X9 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X10 @ X11 @ X9 @ X8 @ X7 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ~ ( m1_subset_1 @ X27 @ sk_D )
      | ( sk_F_1
       != ( k4_mcart_1 @ X28 @ X26 @ X29 @ X27 ) )
      | ( sk_E = X28 )
      | ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X28 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X0 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X10 @ X11 @ X9 @ X8 @ X7 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X10 @ X11 @ X9 @ X8 @ X7 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X10 @ X11 @ X9 @ X8 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
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
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','36','44','52'])).

thf('54',plain,
    ( sk_E
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ sk_E @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k4_zfmisc_1 @ X20 @ X19 @ X18 @ X17 ) )
      | ( ( k8_mcart_1 @ X20 @ X19 @ X18 @ X17 @ X21 )
        = X23 )
      | ( X21
       != ( k4_mcart_1 @ X23 @ X24 @ X25 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_mcart_1 @ X20 @ X19 @ X18 @ X17 @ ( k4_mcart_1 @ X23 @ X24 @ X25 @ X22 ) )
        = X23 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X23 @ X24 @ X25 @ X22 ) @ ( k4_zfmisc_1 @ X20 @ X19 @ X18 @ X17 ) )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ sk_E @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ sk_E @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','54'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
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
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = sk_E ),
    inference('simplify_reflect-',[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = sk_E ),
    inference('sup+',[status(thm)],['7','66'])).

thf('68',plain,(
    sk_E
 != ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('70',plain,(
    sk_E
 != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhOpLa8UXQ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 62 iterations in 0.043s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.54  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.21/0.54  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.54  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(t79_mcart_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.54       ( ( ![G:$i]:
% 0.21/0.54           ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.54             ( ![H:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.54                 ( ![I:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.54                     ( ![J:$i]:
% 0.21/0.54                       ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.54                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.54                           ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.54         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( ( E ) = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.54        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.54          ( ( ![G:$i]:
% 0.21/0.54              ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.54                ( ![H:$i]:
% 0.21/0.54                  ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.54                    ( ![I:$i]:
% 0.21/0.54                      ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.54                        ( ![J:$i]:
% 0.21/0.54                          ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.54                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.54                              ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.54            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54              ( ( E ) = ( k8_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t79_mcart_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t61_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ~( ![E:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.54                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.54                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.54                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.54                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.21/0.54                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         (((X12) = (k1_xboole_0))
% 0.21/0.54          | ((X13) = (k1_xboole_0))
% 0.21/0.54          | ((X14) = (k1_xboole_0))
% 0.21/0.54          | ((k8_mcart_1 @ X12 @ X13 @ X14 @ X16 @ X15)
% 0.21/0.54              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X15))))
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X12 @ X13 @ X14 @ X16))
% 0.21/0.54          | ((X16) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.54            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.54         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l68_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ?[E:$i]:
% 0.21/0.54            ( ( ![F:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.54                  ( ![G:$i]:
% 0.21/0.54                    ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.54                      ( ![H:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.54                          ( ![I:$i]:
% 0.21/0.54                            ( ( m1_subset_1 @ I @ D ) =>
% 0.21/0.54                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.21/0.54              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X7) = (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ((X9) = (k1_xboole_0))
% 0.21/0.54          | ((X10)
% 0.21/0.54              = (k4_mcart_1 @ (sk_F @ X10 @ X11 @ X9 @ X8 @ X7) @ 
% 0.21/0.54                 (sk_G @ X10 @ X11 @ X9 @ X8 @ X7) @ 
% 0.21/0.54                 (sk_H @ X10 @ X11 @ X9 @ X8 @ X7) @ 
% 0.21/0.54                 (sk_I @ X10 @ X11 @ X9 @ X8 @ X7)))
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.21/0.54          | ((X11) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | ((sk_F_1)
% 0.21/0.54            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (((sk_F_1)
% 0.21/0.54         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['11', '12', '13', '14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (((sk_F_1)
% 0.21/0.54         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['11', '12', '13', '14', '15'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X7) = (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ((X9) = (k1_xboole_0))
% 0.21/0.54          | (m1_subset_1 @ (sk_G @ X10 @ X11 @ X9 @ X8 @ X7) @ X8)
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.21/0.54          | ((X11) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['20', '21', '22', '23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X27 @ sk_D)
% 0.21/0.54          | ((sk_F_1) != (k4_mcart_1 @ X28 @ X26 @ X29 @ X27))
% 0.21/0.54          | ((sk_E) = (X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.54          | ((sk_E) = (X0))
% 0.21/0.54          | ((sk_F_1)
% 0.21/0.54              != (k4_mcart_1 @ X0 @ 
% 0.21/0.54                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((((sk_F_1) != (sk_F_1))
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.54        | ((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X7) = (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ((X9) = (k1_xboole_0))
% 0.21/0.54          | (m1_subset_1 @ (sk_I @ X10 @ X11 @ X9 @ X8 @ X7) @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.21/0.54          | ((X11) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['31', '32', '33', '34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X7) = (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ((X9) = (k1_xboole_0))
% 0.21/0.54          | (m1_subset_1 @ (sk_H @ X10 @ X11 @ X9 @ X8 @ X7) @ X9)
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.21/0.54          | ((X11) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['39', '40', '41', '42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X7) = (k1_xboole_0))
% 0.21/0.54          | ((X8) = (k1_xboole_0))
% 0.21/0.54          | ((X9) = (k1_xboole_0))
% 0.21/0.54          | (m1_subset_1 @ (sk_F @ X10 @ X11 @ X9 @ X8 @ X7) @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.21/0.54          | ((X11) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((((sk_D) = (k1_xboole_0))
% 0.21/0.54        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['47', '48', '49', '50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((((sk_F_1) != (sk_F_1))
% 0.21/0.54        | ((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '36', '44', '52'])).
% 0.21/0.54  thf('54', plain, (((sk_E) = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((sk_F_1)
% 0.21/0.54         = (k4_mcart_1 @ sk_E @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '54'])).
% 0.21/0.54  thf(t78_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.54              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.54                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.54                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.54                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.54                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, 
% 0.21/0.54         X24 : $i, X25 : $i]:
% 0.21/0.54         (((X17) = (k1_xboole_0))
% 0.21/0.54          | ((X18) = (k1_xboole_0))
% 0.21/0.54          | ((X19) = (k1_xboole_0))
% 0.21/0.54          | ((X20) = (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ (k4_zfmisc_1 @ X20 @ X19 @ X18 @ X17))
% 0.21/0.54          | ((k8_mcart_1 @ X20 @ X19 @ X18 @ X17 @ X21) = (X23))
% 0.21/0.54          | ((X21) != (k4_mcart_1 @ X23 @ X24 @ X25 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 0.21/0.54         X25 : $i]:
% 0.21/0.54         (((k8_mcart_1 @ X20 @ X19 @ X18 @ X17 @ 
% 0.21/0.54            (k4_mcart_1 @ X23 @ X24 @ X25 @ X22)) = (X23))
% 0.21/0.54          | ~ (m1_subset_1 @ (k4_mcart_1 @ X23 @ X24 @ X25 @ X22) @ 
% 0.21/0.54               (k4_zfmisc_1 @ X20 @ X19 @ X18 @ X17))
% 0.21/0.54          | ((X20) = (k1_xboole_0))
% 0.21/0.54          | ((X19) = (k1_xboole_0))
% 0.21/0.54          | ((X18) = (k1_xboole_0))
% 0.21/0.54          | ((X17) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.54          | ((X0) = (k1_xboole_0))
% 0.21/0.54          | ((X1) = (k1_xboole_0))
% 0.21/0.54          | ((X2) = (k1_xboole_0))
% 0.21/0.54          | ((X3) = (k1_xboole_0))
% 0.21/0.54          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.54              (k4_mcart_1 @ sk_E @ 
% 0.21/0.54               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.54              = (sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (((sk_F_1)
% 0.21/0.54         = (k4_mcart_1 @ sk_E @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '54'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.54          | ((X0) = (k1_xboole_0))
% 0.21/0.54          | ((X1) = (k1_xboole_0))
% 0.21/0.54          | ((X2) = (k1_xboole_0))
% 0.21/0.54          | ((X3) = (k1_xboole_0))
% 0.21/0.54          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '60'])).
% 0.21/0.54  thf('62', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)],
% 0.21/0.54                ['61', '62', '63', '64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) = (sk_E))),
% 0.21/0.54      inference('sup+', [status(thm)], ['7', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((sk_E) != (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.54         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (((sk_E) != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['67', '70'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
