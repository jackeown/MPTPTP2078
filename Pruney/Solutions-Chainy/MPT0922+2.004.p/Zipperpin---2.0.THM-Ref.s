%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bt1vglKECo

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 752 expanded)
%              Number of leaves         :   24 ( 235 expanded)
%              Depth                    :   20
%              Number of atoms          : 1902 (24640 expanded)
%              Number of equality atoms :  253 (3517 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_mcart_1,axiom,(
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

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 ) )
      | ( X30
        = ( k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29 ) )
      | ( m1_subset_1 @ ( sk_I @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_mcart_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('5',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','10'])).

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

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 ) )
      | ( X30
        = ( k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29 ) )
      | ( m1_subset_1 @ ( sk_G @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t81_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 ) )
      | ( X30
        = ( k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29 ) )
      | ( X29
        = ( k4_mcart_1 @ ( sk_G @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ ( sk_H @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ ( sk_I @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ ( sk_J @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t81_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

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
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 ) )
      | ( X30
        = ( k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29 ) )
      | ( m1_subset_1 @ ( sk_H @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t81_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_B )
      | ~ ( m1_subset_1 @ X32 @ sk_D )
      | ( sk_E = X32 )
      | ( sk_F
       != ( k4_mcart_1 @ X33 @ X31 @ X34 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_F
       != ( k4_mcart_1 @ X1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X2 @ X3 ) )
      | ( sk_E = X3 )
      | ~ ( m1_subset_1 @ X3 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_F != sk_F )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 ) )
      | ( X30
        = ( k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29 ) )
      | ( m1_subset_1 @ ( sk_J @ X29 @ X30 @ X28 @ X27 @ X26 @ X25 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t81_mcart_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

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

thf('69',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( ( k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20 )
        = X21 )
      | ( X20
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14 )
        = ( k2_mcart_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('81',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_F )
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( ( k2_mcart_1 @ sk_F )
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_F )
        = sk_E )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('sup+',[status(thm)],['65','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( ( k2_mcart_1 @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('93',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('98',plain,(
    ! [X0: $i] : ( sk_E != X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bt1vglKECo
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 145 iterations in 0.221s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.67  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.67  thf(sk_J_type, type, sk_J: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.67  thf(t82_mcart_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.67       ( ( ![G:$i]:
% 0.46/0.67           ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.67             ( ![H:$i]:
% 0.46/0.67               ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.67                 ( ![I:$i]:
% 0.46/0.67                   ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.67                     ( ![J:$i]:
% 0.46/0.67                       ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.67                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.67                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.67         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.67        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.67          ( ( ![G:$i]:
% 0.46/0.67              ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.67                ( ![H:$i]:
% 0.46/0.67                  ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.67                    ( ![I:$i]:
% 0.46/0.67                      ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.67                        ( ![J:$i]:
% 0.46/0.67                          ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.67                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.67                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.67            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t81_mcart_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.67       ( ( ![G:$i]:
% 0.46/0.67           ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.67             ( ![H:$i]:
% 0.46/0.67               ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.67                 ( ![I:$i]:
% 0.46/0.67                   ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.67                     ( ![J:$i]:
% 0.46/0.67                       ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.67                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.67                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.67         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (((X25) = (k1_xboole_0))
% 0.46/0.67          | ((X26) = (k1_xboole_0))
% 0.46/0.67          | ((X27) = (k1_xboole_0))
% 0.46/0.67          | ((X28) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28))
% 0.46/0.67          | ((X30) = (k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29))
% 0.46/0.67          | (m1_subset_1 @ (sk_I @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ X27))),
% 0.46/0.67      inference('cnf', [status(esa)], [t81_mcart_1])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.46/0.67          | ((X0) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t61_mcart_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.67          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.46/0.67          ( ~( ![E:$i]:
% 0.46/0.67               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.67                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.67                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.46/0.67                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.67                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.46/0.67                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.67                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.46/0.67                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         (((X11) = (k1_xboole_0))
% 0.46/0.67          | ((X12) = (k1_xboole_0))
% 0.46/0.67          | ((X13) = (k1_xboole_0))
% 0.46/0.67          | ((k10_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14)
% 0.46/0.67              = (k2_mcart_1 @ (k1_mcart_1 @ X14)))
% 0.46/0.67          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.46/0.67          | ((X15) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      ((((sk_D) = (k1_xboole_0))
% 0.46/0.67        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ((sk_B) = (k1_xboole_0))
% 0.46/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.67  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['2', '10'])).
% 0.46/0.67  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('15', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['11', '12', '13', '14', '15'])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (((X25) = (k1_xboole_0))
% 0.46/0.67          | ((X26) = (k1_xboole_0))
% 0.46/0.67          | ((X27) = (k1_xboole_0))
% 0.46/0.67          | ((X28) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28))
% 0.46/0.67          | ((X30) = (k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29))
% 0.46/0.67          | (m1_subset_1 @ (sk_G @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ X25))),
% 0.46/0.67      inference('cnf', [status(esa)], [t81_mcart_1])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.67          | ((X0) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.67  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['21', '22', '23', '24', '25'])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (((X25) = (k1_xboole_0))
% 0.46/0.67          | ((X26) = (k1_xboole_0))
% 0.46/0.67          | ((X27) = (k1_xboole_0))
% 0.46/0.67          | ((X28) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28))
% 0.46/0.67          | ((X30) = (k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29))
% 0.46/0.67          | ((X29)
% 0.46/0.67              = (k4_mcart_1 @ (sk_G @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ 
% 0.46/0.67                 (sk_H @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ 
% 0.46/0.67                 (sk_I @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ 
% 0.46/0.67                 (sk_J @ X29 @ X30 @ X28 @ X27 @ X26 @ X25))))),
% 0.46/0.67      inference('cnf', [status(esa)], [t81_mcart_1])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F)
% 0.46/0.67            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67          | ((X0) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F)
% 0.46/0.67            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F)
% 0.46/0.67            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['31', '32', '33', '34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (((X25) = (k1_xboole_0))
% 0.46/0.67          | ((X26) = (k1_xboole_0))
% 0.46/0.67          | ((X27) = (k1_xboole_0))
% 0.46/0.67          | ((X28) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28))
% 0.46/0.67          | ((X30) = (k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29))
% 0.46/0.67          | (m1_subset_1 @ (sk_H @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [t81_mcart_1])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.46/0.67          | ((X0) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.67  thf('42', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('43', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('44', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('45', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['41', '42', '43', '44', '45'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X31 @ sk_B)
% 0.46/0.67          | ~ (m1_subset_1 @ X32 @ sk_D)
% 0.46/0.67          | ((sk_E) = (X32))
% 0.46/0.67          | ((sk_F) != (k4_mcart_1 @ X33 @ X31 @ X34 @ X32))
% 0.46/0.67          | ~ (m1_subset_1 @ X34 @ sk_C)
% 0.46/0.67          | ~ (m1_subset_1 @ X33 @ sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.46/0.67          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.46/0.67          | ((sk_F)
% 0.46/0.67              != (k4_mcart_1 @ X1 @ 
% 0.46/0.67                  (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ X2 @ X3))
% 0.46/0.67          | ((sk_E) = (X3))
% 0.46/0.67          | ~ (m1_subset_1 @ X3 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F) != (sk_F))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_C)
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_A)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['36', '48'])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             sk_A)
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_C)
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['26', '50'])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             sk_C)
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['16', '52'])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               sk_D)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (((X25) = (k1_xboole_0))
% 0.46/0.67          | ((X26) = (k1_xboole_0))
% 0.46/0.67          | ((X27) = (k1_xboole_0))
% 0.46/0.67          | ((X28) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28))
% 0.46/0.67          | ((X30) = (k10_mcart_1 @ X25 @ X26 @ X27 @ X28 @ X29))
% 0.46/0.67          | (m1_subset_1 @ (sk_J @ X29 @ X30 @ X28 @ X27 @ X26 @ X25) @ X28))),
% 0.46/0.67      inference('cnf', [status(esa)], [t81_mcart_1])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.46/0.67          | ((X0) = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.67  thf('58', plain,
% 0.46/0.67      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.67  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('63', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['59', '60', '61', '62', '63'])).
% 0.46/0.67  thf('65', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.67      inference('clc', [status(thm)], ['54', '64'])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F)
% 0.46/0.67            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['31', '32', '33', '34', '35'])).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((sk_F)
% 0.46/0.67            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['31', '32', '33', '34', '35'])).
% 0.46/0.67  thf(t78_mcart_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.67       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.67            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.46/0.67            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.46/0.67              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.46/0.67                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.46/0.67                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.46/0.67                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.46/0.67                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.46/0.67         X23 : $i, X24 : $i]:
% 0.46/0.67         (((X16) = (k1_xboole_0))
% 0.46/0.67          | ((X17) = (k1_xboole_0))
% 0.46/0.67          | ((X18) = (k1_xboole_0))
% 0.46/0.67          | ((X19) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.46/0.67          | ((k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20) = (X21))
% 0.46/0.67          | ((X20) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i, 
% 0.46/0.67         X24 : $i]:
% 0.46/0.67         (((k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ 
% 0.46/0.67            (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)) = (X21))
% 0.46/0.67          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X21) @ 
% 0.46/0.67               (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.46/0.67          | ((X19) = (k1_xboole_0))
% 0.46/0.67          | ((X18) = (k1_xboole_0))
% 0.46/0.67          | ((X17) = (k1_xboole_0))
% 0.46/0.67          | ((X16) = (k1_xboole_0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.67          | ((X4) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k1_xboole_0))
% 0.46/0.67          | ((X1) = (k1_xboole_0))
% 0.46/0.67          | ((X2) = (k1_xboole_0))
% 0.46/0.67          | ((X3) = (k1_xboole_0))
% 0.46/0.67          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.46/0.67              (k4_mcart_1 @ (sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67               (sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67              = (sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['68', '70'])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.46/0.67            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67            = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ((sk_A) = (k1_xboole_0))
% 0.46/0.67          | ((sk_B) = (k1_xboole_0))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((sk_D) = (k1_xboole_0))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['67', '71'])).
% 0.46/0.67  thf('73', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('77', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.46/0.67            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.67             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.67            = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['72', '73', '74', '75', '76'])).
% 0.46/0.67  thf('78', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67            = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['66', '77'])).
% 0.46/0.67  thf('79', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('80', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         (((X11) = (k1_xboole_0))
% 0.46/0.67          | ((X12) = (k1_xboole_0))
% 0.46/0.67          | ((X13) = (k1_xboole_0))
% 0.46/0.67          | ((k11_mcart_1 @ X11 @ X12 @ X13 @ X15 @ X14) = (k2_mcart_1 @ X14))
% 0.46/0.67          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.46/0.67          | ((X15) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.67  thf('81', plain,
% 0.46/0.67      ((((sk_D) = (k1_xboole_0))
% 0.46/0.67        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.46/0.67            = (k2_mcart_1 @ sk_F))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ((sk_B) = (k1_xboole_0))
% 0.46/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.67  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('85', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['81', '82', '83', '84', '85'])).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k2_mcart_1 @ sk_F) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('demod', [status(thm)], ['78', '86'])).
% 0.46/0.67  thf('88', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((k2_mcart_1 @ sk_F)
% 0.46/0.67              = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k2_mcart_1 @ sk_F) = (sk_E))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['65', '88'])).
% 0.46/0.67  thf('90', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.46/0.67          | ((k2_mcart_1 @ sk_F) = (sk_E)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['89'])).
% 0.46/0.67  thf('91', plain,
% 0.46/0.67      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('92', plain,
% 0.46/0.67      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)],
% 0.46/0.67                ['81', '82', '83', '84', '85'])).
% 0.46/0.67  thf('93', plain, (((sk_E) != (k2_mcart_1 @ sk_F))),
% 0.46/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.67  thf('94', plain, (![X0 : $i]: ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.46/0.67  thf('95', plain, (![X0 : $i]: ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.46/0.67  thf('96', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['94', '95'])).
% 0.46/0.67  thf('97', plain, (((sk_E) != (k2_mcart_1 @ sk_F))),
% 0.46/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.67  thf('98', plain, (![X0 : $i]: ((sk_E) != (X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.67  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
