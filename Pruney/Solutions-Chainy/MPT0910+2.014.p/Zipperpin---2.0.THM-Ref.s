%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q9Z3RijW0K

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 348 expanded)
%              Number of leaves         :   25 ( 121 expanded)
%              Depth                    :   16
%              Number of atoms          : 1170 (7238 expanded)
%              Number of equality atoms :  156 (1009 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

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

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k3_zfmisc_1 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
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
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k4_tarski @ ( k4_tarski @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ sk_B )
      | ( sk_D = X21 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X22 @ X21 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ sk_C )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ sk_B )
      | ( sk_D = X21 )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X22 @ X21 ) @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ sk_C )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','30'])).

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
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','35','44'])).

thf('46',plain,
    ( ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( sk_D
    = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','56'])).

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

thf('58',plain,(
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

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X13 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k4_tarski @ ( k4_tarski @ X12 @ X13 ) @ X14 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X16 ) )
      | ( ( k6_mcart_1 @ X10 @ X11 @ X16 @ ( k4_tarski @ ( k4_tarski @ X12 @ X13 ) @ X14 ) )
        = X13 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','56'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['10','71'])).

thf('73',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('75',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q9Z3RijW0K
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 36 iterations in 0.027s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.22/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(t70_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49       ( ( ![F:$i]:
% 0.22/0.49           ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.49             ( ![G:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.49                 ( ![H:$i]:
% 0.22/0.49                   ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.49                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.49                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.22/0.49         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49          ( ( ![F:$i]:
% 0.22/0.49              ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.49                ( ![G:$i]:
% 0.22/0.49                  ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.49                    ( ![H:$i]:
% 0.22/0.49                      ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.49                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.49                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.22/0.49            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t50_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.49                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.49                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.49                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X17) = (k1_xboole_0))
% 0.22/0.49          | ((X18) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X17 @ X18 @ X20 @ X19)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X19)))
% 0.22/0.49          | ~ (m1_subset_1 @ X19 @ (k3_zfmisc_1 @ X17 @ X18 @ X20))
% 0.22/0.49          | ((X20) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X17) = (k1_xboole_0))
% 0.22/0.49          | ((X18) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X17 @ X18 @ X20 @ X19)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X19)))
% 0.22/0.49          | ~ (m1_subset_1 @ X19 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X20))
% 0.22/0.49          | ((X20) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.22/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.49  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(l44_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ?[D:$i]:
% 0.22/0.49            ( ( ![E:$i]:
% 0.22/0.49                ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.49                  ( ![F:$i]:
% 0.22/0.49                    ( ( m1_subset_1 @ F @ B ) =>
% 0.22/0.49                      ( ![G:$i]:
% 0.22/0.49                        ( ( m1_subset_1 @ G @ C ) =>
% 0.22/0.49                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.22/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | ((X8)
% 0.22/0.49              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.22/0.49                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.49  thf(d3_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.22/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | ((X8)
% 0.22/0.49              = (k4_tarski @ 
% 0.22/0.49                 (k4_tarski @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.22/0.49                  (sk_F @ X8 @ X9 @ X7 @ X6)) @ 
% 0.22/0.49                 (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_E_1)
% 0.22/0.49            = (k4_tarski @ 
% 0.22/0.49               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.49                (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.22/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '16'])).
% 0.22/0.49  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((sk_E_1)
% 0.22/0.49         = (k4_tarski @ 
% 0.22/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.22/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((sk_E_1)
% 0.22/0.49         = (k4_tarski @ 
% 0.22/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.22/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X21 @ sk_B)
% 0.22/0.49          | ((sk_D) = (X21))
% 0.22/0.49          | ((sk_E_1) != (k3_mcart_1 @ X22 @ X21 @ X23))
% 0.22/0.49          | ~ (m1_subset_1 @ X23 @ sk_C)
% 0.22/0.49          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.22/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X21 @ sk_B)
% 0.22/0.49          | ((sk_D) = (X21))
% 0.22/0.49          | ((sk_E_1) != (k4_tarski @ (k4_tarski @ X22 @ X21) @ X23))
% 0.22/0.49          | ~ (m1_subset_1 @ X23 @ sk_C)
% 0.22/0.49          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      ((((sk_E_1) != (sk_E_1))
% 0.22/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.49        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.22/0.49        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.49        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.49  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.22/0.49  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      ((((sk_E_1) != (sk_E_1))
% 0.22/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.49        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '35', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      ((((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.22/0.49          | ((X9) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.49  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('54', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['51', '52', '53', '54'])).
% 0.22/0.49  thf('56', plain, (((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['46', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (((sk_E_1)
% 0.22/0.49         = (k4_tarski @ 
% 0.22/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.22/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '56'])).
% 0.22/0.49  thf(t47_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ?[D:$i]:
% 0.22/0.49            ( ( ?[E:$i,F:$i,G:$i]:
% 0.22/0.49                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.22/0.49                       ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.22/0.49                       ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.22/0.49                  ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) & 
% 0.22/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (((X10) = (k1_xboole_0))
% 0.22/0.49          | ((X11) = (k1_xboole_0))
% 0.22/0.49          | ((X15) != (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.22/0.49          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ X15) = (X13))
% 0.22/0.49          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.22/0.49          | ((X16) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.22/0.49         (((X16) = (k1_xboole_0))
% 0.22/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.22/0.49               (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.22/0.49          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.22/0.49              = (X13))
% 0.22/0.49          | ((X11) = (k1_xboole_0))
% 0.22/0.49          | ((X10) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.22/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.22/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.22/0.49         (((X16) = (k1_xboole_0))
% 0.22/0.49          | ~ (m1_subset_1 @ (k4_tarski @ (k4_tarski @ X12 @ X13) @ X14) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X16))
% 0.22/0.49          | ((k6_mcart_1 @ X10 @ X11 @ X16 @ 
% 0.22/0.49              (k4_tarski @ (k4_tarski @ X12 @ X13) @ X14)) = (X13))
% 0.22/0.49          | ((X11) = (k1_xboole_0))
% 0.22/0.49          | ((X10) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.22/0.49          | ((X2) = (k1_xboole_0))
% 0.22/0.49          | ((X1) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.22/0.49              (k4_tarski @ 
% 0.22/0.49               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.22/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.22/0.49              = (sk_D))
% 0.22/0.49          | ((X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['57', '63'])).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      (((sk_E_1)
% 0.22/0.49         = (k4_tarski @ 
% 0.22/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.22/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '56'])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ sk_E_1 @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.22/0.49          | ((X2) = (k1_xboole_0))
% 0.22/0.49          | ((X1) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) = (sk_D))
% 0.22/0.49          | ((X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '66'])).
% 0.22/0.49  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('70', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('71', plain, (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['67', '68', '69', '70'])).
% 0.22/0.49  thf('72', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D))),
% 0.22/0.49      inference('sup+', [status(thm)], ['10', '71'])).
% 0.22/0.49  thf('73', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.22/0.49  thf('75', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.49  thf('76', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['72', '75'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
