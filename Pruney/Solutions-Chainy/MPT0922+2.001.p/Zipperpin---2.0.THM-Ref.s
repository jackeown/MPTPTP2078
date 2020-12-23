%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.plHAxSRWNY

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 (3107 expanded)
%              Number of leaves         :   28 ( 971 expanded)
%              Depth                    :   26
%              Number of atoms          : 2053 (88338 expanded)
%              Number of equality atoms :  265 (11974 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X28 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17
        = ( k4_mcart_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17
        = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) ) @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('23',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('24',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('26',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ sk_B )
      | ~ ( m1_subset_1 @ X34 @ sk_D )
      | ( sk_E = X34 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X35 @ X33 @ X36 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('34',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ sk_B )
      | ~ ( m1_subset_1 @ X34 @ sk_D )
      | ( sk_E = X34 )
      | ( sk_F_1
       != ( k3_mcart_1 @ ( k4_tarski @ X35 @ X33 ) @ X36 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X35 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F_1
       != ( k3_mcart_1 @ ( k4_tarski @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('39',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
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
    m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
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
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('55',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','44','52','60'])).

thf('62',plain,
    ( sk_E
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['22','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['22','62'])).

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

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X26
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( ( k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26 )
        = X22 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
        = X22 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) )
        = X22 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['22','62'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X26
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( ( k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26 )
        = X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('84',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
        = X23 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) )
        = X23 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['91','92','93','94','95'])).

thf('97',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['80','96'])).

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X26
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
      | ( ( k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26 )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t59_mcart_1])).

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 ) )
        = X25 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('101',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k3_mcart_1 @ ( k4_tarski @ X6 @ X7 ) @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('102',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27 ) )
      | ( ( k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ ( k3_mcart_1 @ ( k4_tarski @ X22 @ X23 ) @ X24 @ X25 ) )
        = X25 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,
    ( sk_F_1
    = ( k3_mcart_1 @ ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['80','96'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','105'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = sk_E ),
    inference('simplify_reflect-',[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = sk_E ),
    inference('sup+',[status(thm)],['7','111'])).

thf('113',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('115',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.plHAxSRWNY
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 114 iterations in 0.081s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.20/0.55  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(t82_mcart_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.55       ( ( ![G:$i]:
% 0.20/0.55           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.55             ( ![H:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.55                 ( ![I:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.55                     ( ![J:$i]:
% 0.20/0.55                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.55                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.55                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.55         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.55          ( ( ![G:$i]:
% 0.20/0.55              ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.55                ( ![H:$i]:
% 0.20/0.55                  ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.55                    ( ![I:$i]:
% 0.20/0.55                      ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.55                        ( ![J:$i]:
% 0.20/0.55                          ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.55                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.55                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.55            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t61_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ~( ![E:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.55                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.55                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.55                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.55                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.55         (((X28) = (k1_xboole_0))
% 0.20/0.55          | ((X29) = (k1_xboole_0))
% 0.20/0.55          | ((X30) = (k1_xboole_0))
% 0.20/0.55          | ((k11_mcart_1 @ X28 @ X29 @ X30 @ X32 @ X31) = (k2_mcart_1 @ X31))
% 0.20/0.55          | ~ (m1_subset_1 @ X31 @ (k4_zfmisc_1 @ X28 @ X29 @ X30 @ X32))
% 0.20/0.55          | ((X32) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55            = (k2_mcart_1 @ sk_F_1))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55         = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(l68_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ?[E:$i]:
% 0.20/0.55            ( ( ![F:$i]:
% 0.20/0.55                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.55                  ( ![G:$i]:
% 0.20/0.55                    ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.55                      ( ![H:$i]:
% 0.20/0.55                        ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.55                          ( ![I:$i]:
% 0.20/0.55                            ( ( m1_subset_1 @ I @ D ) =>
% 0.20/0.55                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.20/0.55              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | ((X17)
% 0.20/0.55              = (k4_mcart_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.55                 (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.55                 (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.55                 (sk_I @ X17 @ X18 @ X16 @ X15 @ X14)))
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.55  thf(d4_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.55       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.55  thf(d3_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.55           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | ((X17)
% 0.20/0.55              = (k3_mcart_1 @ 
% 0.20/0.55                 (k4_tarski @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.55                  (sk_G @ X17 @ X18 @ X16 @ X15 @ X14)) @ 
% 0.20/0.55                 (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.55                 (sk_I @ X17 @ X18 @ X16 @ X15 @ X14)))
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | ((sk_F_1)
% 0.20/0.55            = (k3_mcart_1 @ 
% 0.20/0.55               (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55                (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.55  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['17', '18', '19', '20', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['17', '18', '19', '20', '21'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | (m1_subset_1 @ (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ X15)
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('30', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['26', '27', '28', '29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X33 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ sk_D)
% 0.20/0.55          | ((sk_E) = (X34))
% 0.20/0.55          | ((sk_F_1) != (k4_mcart_1 @ X35 @ X33 @ X36 @ X34))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X33 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ sk_D)
% 0.20/0.55          | ((sk_E) = (X34))
% 0.20/0.55          | ((sk_F_1) != (k3_mcart_1 @ (k4_tarski @ X35 @ X33) @ X36 @ X34))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.55          | ((sk_F_1)
% 0.20/0.55              != (k3_mcart_1 @ 
% 0.20/0.55                  (k4_tarski @ X0 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55                  X1 @ X2))
% 0.20/0.55          | ((sk_E) = (X2))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((((sk_F_1) != (sk_F_1))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.55        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | (m1_subset_1 @ (sk_I @ X17 @ X18 @ X16 @ X15 @ X14) @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['39', '40', '41', '42', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | (m1_subset_1 @ (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ X16)
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['47', '48', '49', '50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (((X14) = (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | ((X16) = (k1_xboole_0))
% 0.20/0.55          | (m1_subset_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ X14)
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.55  thf('56', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('58', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('59', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['55', '56', '57', '58', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      ((((sk_F_1) != (sk_F_1))
% 0.20/0.55        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['36', '44', '52', '60'])).
% 0.20/0.55  thf('62', plain, (((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '62'])).
% 0.20/0.55  thf(t59_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ?[E:$i]:
% 0.20/0.55            ( ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.55                ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.20/0.55                       ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.20/0.55                       ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.20/0.55                       ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.20/0.55                  ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) & 
% 0.20/0.55              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X26 : $i, X27 : $i]:
% 0.20/0.55         (((X19) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X26) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.55          | ((k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26) = (X22))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((X27) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k4_mcart_1 @ X22 @ X23 @ X24 @ X25)) = (X22))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k8_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25)) = (X22))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.55              (k3_mcart_1 @ 
% 0.20/0.55               (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55                (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.20/0.55              = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['65', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '62'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k8_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.20/0.55              = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55            = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['64', '73'])).
% 0.20/0.55  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('78', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['74', '75', '76', '77', '78'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '79'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X26 : $i, X27 : $i]:
% 0.20/0.55         (((X19) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X26) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.55          | ((k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26) = (X23))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((X27) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k4_mcart_1 @ X22 @ X23 @ X24 @ X25)) = (X23))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k9_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25)) = (X23))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.55              (k3_mcart_1 @ 
% 0.20/0.55               (k4_tarski @ 
% 0.20/0.55                (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55                (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.20/0.55              = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['82', '87'])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55             (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '79'])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.20/0.55              = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55            = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['81', '90'])).
% 0.20/0.55  thf('92', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('93', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('94', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['91', '92', '93', '94', '95'])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55             (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X26 : $i, X27 : $i]:
% 0.20/0.55         (((X19) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X26) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X25))
% 0.20/0.55          | ((k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ X26) = (X25))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((X27) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t59_mcart_1])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k4_mcart_1 @ X22 @ X23 @ X24 @ X25)) = (X25))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k3_mcart_1 @ (k4_tarski @ X6 @ X7) @ X8 @ X9))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.55         X27 : $i]:
% 0.20/0.55         (((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25) @ 
% 0.20/0.55               (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X27))
% 0.20/0.55          | ((k11_mcart_1 @ X19 @ X20 @ X21 @ X27 @ 
% 0.20/0.55              (k3_mcart_1 @ (k4_tarski @ X22 @ X23) @ X24 @ X25)) = (X25))
% 0.20/0.55          | ((X21) = (k1_xboole_0))
% 0.20/0.55          | ((X20) = (k1_xboole_0))
% 0.20/0.55          | ((X19) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.20/0.55              (k3_mcart_1 @ 
% 0.20/0.55               (k4_tarski @ 
% 0.20/0.55                (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55                (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)) @ 
% 0.20/0.55               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.20/0.55              = (sk_E))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['97', '102'])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (((sk_F_1)
% 0.20/0.55         = (k3_mcart_1 @ 
% 0.20/0.55            (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.20/0.55             (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)) @ 
% 0.20/0.55            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '96'])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      ((((sk_D) = (k1_xboole_0))
% 0.20/0.55        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '105'])).
% 0.20/0.55  thf('107', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('109', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('110', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)],
% 0.20/0.55                ['106', '107', '108', '109', '110'])).
% 0.20/0.55  thf('112', plain, (((k2_mcart_1 @ sk_F_1) = (sk_E))),
% 0.20/0.55      inference('sup+', [status(thm)], ['7', '111'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.55         = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.55  thf('115', plain, (((sk_E) != (k2_mcart_1 @ sk_F_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['113', '114'])).
% 0.20/0.55  thf('116', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
