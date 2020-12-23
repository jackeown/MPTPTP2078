%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uXxl9RRIz9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 298 expanded)
%              Number of leaves         :   25 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  950 (6064 expanded)
%              Number of equality atoms :  125 ( 847 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
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

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('12',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ sk_B )
      | ( sk_D = X17 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X18 @ X17 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ sk_C )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ( sk_D
        = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','32','41'])).

thf('43',plain,
    ( sk_D
    = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','43'])).

thf('45',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','43'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('46',plain,(
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

thf('47',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t50_mcart_1,axiom,(
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

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X13 @ X12 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k3_zfmisc_1 @ X10 @ X11 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X13 @ X12 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uXxl9RRIz9
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 38 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t70_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48       ( ( ![F:$i]:
% 0.21/0.48           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.48             ( ![G:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.48                 ( ![H:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.48                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.48                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.21/0.48         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48          ( ( ![F:$i]:
% 0.21/0.48              ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.48                ( ![G:$i]:
% 0.21/0.48                  ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.48                    ( ![H:$i]:
% 0.21/0.48                      ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.48                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.48                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.21/0.48            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(l44_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ?[D:$i]:
% 0.21/0.48            ( ( ![E:$i]:
% 0.21/0.48                ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.48                  ( ![F:$i]:
% 0.21/0.48                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                      ( ![G:$i]:
% 0.21/0.48                        ( ( m1_subset_1 @ G @ C ) =>
% 0.21/0.48                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.21/0.48              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8)
% 0.21/0.48              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.21/0.48                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((X8)
% 0.21/0.48              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.21/0.48                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_E_1)
% 0.21/0.48            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X17 @ sk_B)
% 0.21/0.48          | ((sk_D) = (X17))
% 0.21/0.48          | ((sk_E_1) != (k3_mcart_1 @ X18 @ X17 @ X19))
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ sk_C)
% 0.21/0.48          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.48          | ((sk_E_1)
% 0.21/0.48              != (k3_mcart_1 @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1))
% 0.21/0.48          | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((sk_E_1) != (sk_E_1))
% 0.21/0.48        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.48        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.48  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      ((((sk_E_1) != (sk_E_1))
% 0.21/0.48        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '32', '41'])).
% 0.21/0.48  thf('43', plain, (((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.21/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.21/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '43'])).
% 0.21/0.48  thf(d3_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.48  thf(t7_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (((k2_mcart_1 @ sk_E_1) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['45', '48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.21/0.48            (k2_mcart_1 @ sk_E_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['44', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (((k1_mcart_1 @ sk_E_1)
% 0.21/0.48         = (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D))),
% 0.21/0.48      inference('sup+', [status(thm)], ['50', '53'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('56', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D))),
% 0.21/0.48      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.48  thf('57', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t50_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ~( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (((X10) = (k1_xboole_0))
% 0.21/0.48          | ((X11) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X10 @ X11 @ X13 @ X12)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X12)))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k3_zfmisc_1 @ X10 @ X11 @ X13))
% 0.21/0.48          | ((X13) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (((X10) = (k1_xboole_0))
% 0.21/0.48          | ((X11) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X10 @ X11 @ X13 @ X12)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X12)))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X13))
% 0.21/0.48          | ((X13) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.21/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.48  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.21/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.48  thf('67', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['57', '66'])).
% 0.21/0.48  thf('68', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['56', '67'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
