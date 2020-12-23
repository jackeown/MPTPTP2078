%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CdD8xH37J0

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 263 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  842 (5861 expanded)
%              Number of equality atoms :  107 ( 846 expanded)
%              Maximal formula depth    :   21 (   7 average)

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_mcart_1,conjecture,(
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
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = F ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
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

thf('6',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('8',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ sk_B )
      | ( sk_D = X18 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X18 @ X17 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ sk_C )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
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
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','24','31'])).

thf('33',plain,
    ( sk_D
    = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','33'])).

thf('35',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','33'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('36',plain,(
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

thf('37',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X13
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k6_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k7_mcart_1 @ X10 @ X11 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('50',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51','52','53'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('57',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('60',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('62',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['47','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CdD8xH37J0
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 45 iterations in 0.025s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t69_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48       ( ( ![F:$i]:
% 0.20/0.48           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.48             ( ![G:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.48                 ( ![H:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.48                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.48                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.20/0.48         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48          ( ( ![F:$i]:
% 0.20/0.48              ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.48                ( ![G:$i]:
% 0.20/0.48                  ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.48                    ( ![H:$i]:
% 0.20/0.48                      ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.48                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.48                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.20/0.48            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l44_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ?[D:$i]:
% 0.20/0.48            ( ( ![E:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.48                  ( ![F:$i]:
% 0.20/0.48                    ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.48                      ( ![G:$i]:
% 0.20/0.48                        ( ( m1_subset_1 @ G @ C ) =>
% 0.20/0.48                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.20/0.48              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((X6) = (k1_xboole_0))
% 0.20/0.48          | ((X7) = (k1_xboole_0))
% 0.20/0.48          | ((X8)
% 0.20/0.48              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.20/0.48                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.20/0.48          | ((X9) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_E_1)
% 0.20/0.48            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((X6) = (k1_xboole_0))
% 0.20/0.48          | ((X7) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.20/0.48          | ((X9) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X17 @ sk_B)
% 0.20/0.48          | ((sk_D) = (X18))
% 0.20/0.48          | ((sk_E_1) != (k3_mcart_1 @ X18 @ X17 @ X19))
% 0.20/0.48          | ~ (m1_subset_1 @ X19 @ sk_C)
% 0.20/0.48          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.48          | ((sk_E_1)
% 0.20/0.48              != (k3_mcart_1 @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1))
% 0.20/0.48          | ((sk_D) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((sk_E_1) != (sk_E_1))
% 0.20/0.48        | ((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.48        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((X6) = (k1_xboole_0))
% 0.20/0.48          | ((X7) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.20/0.48          | ((X9) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((X6) = (k1_xboole_0))
% 0.20/0.48          | ((X7) = (k1_xboole_0))
% 0.20/0.48          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.20/0.48          | ((X9) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((((sk_E_1) != (sk_E_1))
% 0.20/0.48        | ((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '24', '31'])).
% 0.20/0.48  thf('33', plain, (((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '33'])).
% 0.20/0.48  thf(d3_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf(t7_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((k2_mcart_1 @ sk_E_1) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48            (k2_mcart_1 @ sk_E_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((k1_mcart_1 @ sk_E_1)
% 0.20/0.48         = (k4_tarski @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('46', plain, (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D))),
% 0.20/0.48      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t48_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48                 ( ( D ) =
% 0.20/0.48                   ( k3_mcart_1 @
% 0.20/0.48                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.48                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.48                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (((X10) = (k1_xboole_0))
% 0.20/0.48          | ((X11) = (k1_xboole_0))
% 0.20/0.48          | ((X13)
% 0.20/0.48              = (k3_mcart_1 @ (k5_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.20/0.48                 (k6_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.20/0.48                 (k7_mcart_1 @ X10 @ X11 @ X12 @ X13)))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 0.20/0.48          | ((X12) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((sk_E_1)
% 0.20/0.48            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('53', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((k2_mcart_1 @ sk_E_1) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((sk_E_1)
% 0.20/0.48         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (((k1_mcart_1 @ sk_E_1)
% 0.20/0.48         = (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.20/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.20/0.48         = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.48  thf('63', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '62'])).
% 0.20/0.48  thf('64', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['46', '63'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
