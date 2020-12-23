%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uS4emv8vIY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 (1030 expanded)
%              Number of leaves         :   28 ( 334 expanded)
%              Depth                    :   20
%              Number of atoms          : 1320 (27324 expanded)
%              Number of equality atoms :  164 (3636 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17
        = ( k4_mcart_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
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
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('9',plain,(
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

thf('10',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('25',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('36',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('42',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('44',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( m1_subset_1 @ X28 @ sk_D )
      | ( sk_E = X28 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X29 @ X27 @ X30 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D )
    | ( sk_E
      = ( k2_mcart_1 @ sk_F_1 ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('55',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('57',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

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

thf('62',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('65',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('82',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['52','62','72','82'])).

thf('84',plain,
    ( sk_E
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X19 @ X20 @ X21 @ X23 @ X22 )
        = ( k2_mcart_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('88',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ sk_F_1 ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F_1 ) ),
    inference(demod,[status(thm)],['85','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uS4emv8vIY
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 77 iterations in 0.049s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(t82_mcart_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.50       ( ( ![G:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.50             ( ![H:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.50                 ( ![I:$i]:
% 0.20/0.50                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.50                     ( ![J:$i]:
% 0.20/0.50                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.50                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.50                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.50          ( ( ![G:$i]:
% 0.20/0.50              ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.50                ( ![H:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.50                    ( ![I:$i]:
% 0.20/0.50                      ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.50                        ( ![J:$i]:
% 0.20/0.50                          ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.50                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.50                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l68_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ?[E:$i]:
% 0.20/0.50            ( ( ![F:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.50                  ( ![G:$i]:
% 0.20/0.50                    ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.50                      ( ![H:$i]:
% 0.20/0.50                        ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.50                          ( ![I:$i]:
% 0.20/0.50                            ( ( m1_subset_1 @ I @ D ) =>
% 0.20/0.50                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.20/0.50              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | ((X17)
% 0.20/0.50              = (k4_mcart_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.50                 (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.50                 (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.20/0.50                 (sk_I @ X17 @ X18 @ X16 @ X15 @ X14)))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.50          | ((X18) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | ((sk_F_1)
% 0.20/0.50            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.50  thf(d4_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.50       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.50           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((k2_mcart_1 @ sk_F_1) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.50           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.50           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((k1_mcart_1 @ sk_F_1)
% 0.20/0.50         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf(d3_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((k1_mcart_1 @ sk_F_1)
% 0.20/0.50         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((k1_mcart_1 @ sk_F_1)
% 0.20/0.50         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.20/0.50         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.20/0.50         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.20/0.50         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((sk_F_1)
% 0.20/0.50         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.50          | ((X18) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.20/0.50         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50           sk_B)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50        sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)],
% 0.20/0.50                ['44', '45', '46', '47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X28 @ sk_D)
% 0.20/0.50          | ((sk_E) = (X28))
% 0.20/0.50          | ((sk_F_1) != (k4_mcart_1 @ X29 @ X27 @ X30 @ X28))
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ sk_C)
% 0.20/0.50          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.50          | ((sk_F_1)
% 0.20/0.50              != (k4_mcart_1 @ X0 @ 
% 0.20/0.50                  (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ X1 @ X2))
% 0.20/0.50          | ((sk_E) = (X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((((sk_F_1) != (sk_F_1))
% 0.20/0.50        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)
% 0.20/0.50        | ((sk_E) = (k2_mcart_1 @ sk_F_1))
% 0.20/0.50        | ~ (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ sk_C)
% 0.20/0.50        | ~ (m1_subset_1 @ 
% 0.20/0.50             (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_I @ X17 @ X18 @ X16 @ X15 @ X14) @ X18)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.50          | ((X18) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((k2_mcart_1 @ sk_F_1) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('62', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)],
% 0.20/0.50                ['57', '58', '59', '60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.50          | ((X18) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('69', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)],
% 0.20/0.50                ['65', '66', '67', '68', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.20/0.50         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.20/0.50          | ((X18) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('78', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('79', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)],
% 0.20/0.50                ['75', '76', '77', '78', '79'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.20/0.50         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.20/0.50        sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      ((((sk_F_1) != (sk_F_1)) | ((sk_E) = (k2_mcart_1 @ sk_F_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '62', '72', '82'])).
% 0.20/0.50  thf('84', plain, (((sk_E) = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t61_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ~( ![E:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.50                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.50                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.50                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.50                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         (((X19) = (k1_xboole_0))
% 0.20/0.50          | ((X20) = (k1_xboole_0))
% 0.20/0.50          | ((X21) = (k1_xboole_0))
% 0.20/0.50          | ((k11_mcart_1 @ X19 @ X20 @ X21 @ X23 @ X22) = (k2_mcart_1 @ X22))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23))
% 0.20/0.50          | ((X23) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((((sk_D) = (k1_xboole_0))
% 0.20/0.50        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.50            = (k2_mcart_1 @ sk_F_1))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.50  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('92', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.20/0.50         = (k2_mcart_1 @ sk_F_1))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)],
% 0.20/0.50                ['88', '89', '90', '91', '92'])).
% 0.20/0.50  thf('94', plain, (((sk_E) != (k2_mcart_1 @ sk_F_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['85', '93'])).
% 0.20/0.50  thf('95', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['84', '94'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
