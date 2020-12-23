%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.84hu7KT642

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 (2506 expanded)
%              Number of leaves         :   24 ( 765 expanded)
%              Depth                    :   26
%              Number of atoms          : 1798 (80676 expanded)
%              Number of equality atoms :  249 (11333 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(t81_mcart_1,conjecture,(
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
                         => ( E = I ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = I ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_mcart_1])).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
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
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14
        = ( k4_mcart_1 @ ( sk_F @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_G @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_H @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_I @ X14 @ X15 @ X13 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ~ ( m1_subset_1 @ X31 @ sk_D )
      | ( sk_F_1
       != ( k4_mcart_1 @ X32 @ X30 @ X33 @ X31 ) )
      | ( sk_E = X33 )
      | ~ ( m1_subset_1 @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X1 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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
      = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','36','44','52'])).

thf('54',plain,
    ( sk_E
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','54'])).

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

thf('58',plain,(
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

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X19 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','54'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X20 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('80',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
      = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','91'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24 ) )
      | ( ( k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ ( k4_mcart_1 @ X19 @ X20 @ X21 @ X22 ) )
        = X21 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_E @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','91'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = sk_E ),
    inference('simplify_reflect-',[status(thm)],['98','99','100','101','102'])).

thf('104',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = sk_E ),
    inference('sup+',[status(thm)],['7','103'])).

thf('105',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('107',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.84hu7KT642
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 95 iterations in 0.064s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.21/0.53  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(t81_mcart_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.53       ( ( ![G:$i]:
% 0.21/0.53           ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.53             ( ![H:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.53                 ( ![I:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.53                     ( ![J:$i]:
% 0.21/0.53                       ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.53                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.53                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.53         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.53        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.53          ( ( ![G:$i]:
% 0.21/0.53              ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.53                ( ![H:$i]:
% 0.21/0.53                  ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.53                    ( ![I:$i]:
% 0.21/0.53                      ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.53                        ( ![J:$i]:
% 0.21/0.53                          ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.53                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.53                              ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.53            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53              ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t81_mcart_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t61_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ~( ![E:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.53                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.53                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.53                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.21/0.53                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.53         (((X25) = (k1_xboole_0))
% 0.21/0.53          | ((X26) = (k1_xboole_0))
% 0.21/0.53          | ((X27) = (k1_xboole_0))
% 0.21/0.53          | ((k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.21/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.21/0.53          | ((X29) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l68_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ?[E:$i]:
% 0.21/0.53            ( ( ![F:$i]:
% 0.21/0.53                ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.53                  ( ![G:$i]:
% 0.21/0.53                    ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.53                      ( ![H:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.53                          ( ![I:$i]:
% 0.21/0.53                            ( ( m1_subset_1 @ I @ D ) =>
% 0.21/0.53                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.21/0.53              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0))
% 0.21/0.53          | ((X12) = (k1_xboole_0))
% 0.21/0.53          | ((X13) = (k1_xboole_0))
% 0.21/0.53          | ((X14)
% 0.21/0.53              = (k4_mcart_1 @ (sk_F @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.53                 (sk_G @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.53                 (sk_H @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.53                 (sk_I @ X14 @ X15 @ X13 @ X12 @ X11)))
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.53          | ((X15) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((sk_F_1)
% 0.21/0.53            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['11', '12', '13', '14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['11', '12', '13', '14', '15'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0))
% 0.21/0.53          | ((X12) = (k1_xboole_0))
% 0.21/0.53          | ((X13) = (k1_xboole_0))
% 0.21/0.53          | (m1_subset_1 @ (sk_G @ X14 @ X15 @ X13 @ X12 @ X11) @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.53          | ((X15) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['20', '21', '22', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X31 @ sk_D)
% 0.21/0.53          | ((sk_F_1) != (k4_mcart_1 @ X32 @ X30 @ X33 @ X31))
% 0.21/0.53          | ((sk_E) = (X33))
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ sk_C)
% 0.21/0.53          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.53          | ((sk_E) = (X1))
% 0.21/0.53          | ((sk_F_1)
% 0.21/0.53              != (k4_mcart_1 @ X0 @ 
% 0.21/0.53                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((((sk_F_1) != (sk_F_1))
% 0.21/0.53        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.53        | ((sk_E) = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.53        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0))
% 0.21/0.53          | ((X12) = (k1_xboole_0))
% 0.21/0.53          | ((X13) = (k1_xboole_0))
% 0.21/0.53          | (m1_subset_1 @ (sk_I @ X14 @ X15 @ X13 @ X12 @ X11) @ X15)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.53          | ((X15) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['31', '32', '33', '34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0))
% 0.21/0.53          | ((X12) = (k1_xboole_0))
% 0.21/0.53          | ((X13) = (k1_xboole_0))
% 0.21/0.53          | (m1_subset_1 @ (sk_H @ X14 @ X15 @ X13 @ X12 @ X11) @ X13)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.53          | ((X15) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['39', '40', '41', '42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0))
% 0.21/0.53          | ((X12) = (k1_xboole_0))
% 0.21/0.53          | ((X13) = (k1_xboole_0))
% 0.21/0.53          | (m1_subset_1 @ (sk_F @ X14 @ X15 @ X13 @ X12 @ X11) @ X11)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.53          | ((X15) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['47', '48', '49', '50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((((sk_F_1) != (sk_F_1))
% 0.21/0.53        | ((sk_E) = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '36', '44', '52'])).
% 0.21/0.53  thf('54', plain, (((sk_E) = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '54'])).
% 0.21/0.53  thf(t59_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ?[E:$i]:
% 0.21/0.53            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.53                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.53                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.53                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.53                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.53                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.21/0.53              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X23 : $i, X24 : $i]:
% 0.21/0.53         (((X16) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.21/0.53          | ((k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X19))
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((X24) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X24 : $i]:
% 0.21/0.53         (((X24) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.21/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((k8_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.21/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X19))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X16) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.53              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.53              = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '54'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.21/0.53              = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53            = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '62'])).
% 0.21/0.53  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['63', '64', '65', '66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '68'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X23 : $i, X24 : $i]:
% 0.21/0.53         (((X16) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.21/0.53          | ((k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X20))
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((X24) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X24 : $i]:
% 0.21/0.53         (((X24) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.21/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((k9_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.21/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X20))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X16) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.53              (k4_mcart_1 @ 
% 0.21/0.53               (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.53              = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['71', '73'])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '68'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.21/0.53              = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53            = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['70', '76'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.53         (((X25) = (k1_xboole_0))
% 0.21/0.53          | ((X26) = (k1_xboole_0))
% 0.21/0.53          | ((X27) = (k1_xboole_0))
% 0.21/0.53          | ((k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.21/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.21/0.53          | ((X29) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['80', '81', '82', '83', '84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.21/0.53            = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['77', '85'])).
% 0.21/0.53  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('89', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.21/0.53         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['86', '87', '88', '89', '90'])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['69', '91'])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X23 : $i, X24 : $i]:
% 0.21/0.53         (((X16) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X23) != (k4_mcart_1 @ X19 @ X20 @ X21 @ X22))
% 0.21/0.53          | ((k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ X23) = (X21))
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((X24) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.53         X24 : $i]:
% 0.21/0.53         (((X24) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ (k4_mcart_1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.21/0.53               (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X24))
% 0.21/0.53          | ((k10_mcart_1 @ X16 @ X17 @ X18 @ X24 @ 
% 0.21/0.53              (k4_mcart_1 @ X19 @ X20 @ X21 @ X22)) = (X21))
% 0.21/0.53          | ((X18) = (k1_xboole_0))
% 0.21/0.53          | ((X17) = (k1_xboole_0))
% 0.21/0.53          | ((X16) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.53              (k4_mcart_1 @ 
% 0.21/0.53               (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ sk_E @ 
% 0.21/0.53               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.53              = (sk_E))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['92', '94'])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      (((sk_F_1)
% 0.21/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ sk_E @ 
% 0.21/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['69', '91'])).
% 0.21/0.53  thf('97', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53          | ((X3) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['95', '96'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      ((((sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.21/0.53        | ((sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '97'])).
% 0.21/0.53  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('100', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('102', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)],
% 0.21/0.53                ['98', '99', '100', '101', '102'])).
% 0.21/0.53  thf('104', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) = (sk_E))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '103'])).
% 0.21/0.53  thf('105', plain,
% 0.21/0.53      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.53  thf('107', plain, (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.53  thf('108', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['104', '107'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
