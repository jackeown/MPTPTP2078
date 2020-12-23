%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZzVudHwyQv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 152 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  847 (3184 expanded)
%              Number of equality atoms :  110 ( 455 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t71_mcart_1,conjecture,(
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
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X19
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X16 @ X17 @ X18 @ X19 ) @ ( k6_mcart_1 @ X16 @ X17 @ X18 @ X19 ) @ ( k7_mcart_1 @ X16 @ X17 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X19
        = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ X16 @ X17 @ X18 @ X19 ) @ ( k6_mcart_1 @ X16 @ X17 @ X18 @ X19 ) ) @ ( k7_mcart_1 @ X16 @ X17 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14 = X12 )
      | ( ( k3_mcart_1 @ X11 @ X14 @ X15 )
       != ( k3_mcart_1 @ X10 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('10',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X11 @ X14 @ X15 ) )
      = X14 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( k4_tarski @ X11 @ X14 ) @ X15 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_E_1 @ X0 ) )
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k4_tarski @ ( k4_tarski @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('24',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
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
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ sk_B )
      | ( sk_E_1
       != ( k3_mcart_1 @ X21 @ X20 @ X22 ) )
      | ( sk_D = X22 )
      | ~ ( m1_subset_1 @ X22 @ sk_C )
      | ~ ( m1_subset_1 @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ sk_B )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X21 @ X20 ) @ X22 ) )
      | ( sk_D = X22 )
      | ~ ( m1_subset_1 @ X22 @ sk_C )
      | ~ ( m1_subset_1 @ X21 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf('50',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','42','49'])).

thf('51',plain,
    ( sk_D
    = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['22','51'])).

thf('53',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( k4_tarski @ X11 @ X14 ) @ X15 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_E_1 @ X0 ) )
      = sk_D ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_D
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(demod,[status(thm)],['13','54'])).

thf('56',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZzVudHwyQv
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 49 iterations in 0.035s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.19/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.19/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(t71_mcart_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.49       ( ( ![F:$i]:
% 0.19/0.49           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.49             ( ![G:$i]:
% 0.19/0.49               ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.49                 ( ![H:$i]:
% 0.19/0.49                   ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.49                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.49                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.49         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.49          ( ( ![F:$i]:
% 0.19/0.49              ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.49                ( ![G:$i]:
% 0.19/0.49                  ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.49                    ( ![H:$i]:
% 0.19/0.49                      ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.49                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.49                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.49            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t48_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ~( ![D:$i]:
% 0.19/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.49                 ( ( D ) =
% 0.19/0.49                   ( k3_mcart_1 @
% 0.19/0.49                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.49                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.49                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (((X16) = (k1_xboole_0))
% 0.19/0.49          | ((X17) = (k1_xboole_0))
% 0.19/0.49          | ((X19)
% 0.19/0.49              = (k3_mcart_1 @ (k5_mcart_1 @ X16 @ X17 @ X18 @ X19) @ 
% 0.19/0.49                 (k6_mcart_1 @ X16 @ X17 @ X18 @ X19) @ 
% 0.19/0.49                 (k7_mcart_1 @ X16 @ X17 @ X18 @ X19)))
% 0.19/0.49          | ~ (m1_subset_1 @ X19 @ (k3_zfmisc_1 @ X16 @ X17 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.19/0.49  thf(d3_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (((X16) = (k1_xboole_0))
% 0.19/0.49          | ((X17) = (k1_xboole_0))
% 0.19/0.49          | ((X19)
% 0.19/0.49              = (k4_tarski @ 
% 0.19/0.49                 (k4_tarski @ (k5_mcart_1 @ X16 @ X17 @ X18 @ X19) @ 
% 0.19/0.49                  (k6_mcart_1 @ X16 @ X17 @ X18 @ X19)) @ 
% 0.19/0.49                 (k7_mcart_1 @ X16 @ X17 @ X18 @ X19)))
% 0.19/0.49          | ~ (m1_subset_1 @ X19 @ (k3_zfmisc_1 @ X16 @ X17 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_E_1)
% 0.19/0.49            = (k4_tarski @ 
% 0.19/0.49               (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.49                (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)) @ 
% 0.19/0.49               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.49  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (((sk_E_1)
% 0.19/0.49         = (k4_tarski @ 
% 0.19/0.49            (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.49             (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)) @ 
% 0.19/0.49            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7'])).
% 0.19/0.49  thf(t28_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.49     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.19/0.49       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (((X14) = (X12))
% 0.19/0.49          | ((k3_mcart_1 @ X11 @ X14 @ X15) != (k3_mcart_1 @ X10 @ X12 @ X13)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (('#_fresh_sk2' @ (k3_mcart_1 @ X11 @ X14 @ X15)) = (X14))),
% 0.19/0.49      inference('inj_rec', [status(thm)], ['9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (('#_fresh_sk2' @ (k4_tarski @ (k4_tarski @ X11 @ X14) @ X15)) = (X14))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (('#_fresh_sk2' @ (k4_tarski @ sk_E_1 @ X0))
% 0.19/0.49           = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['8', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l44_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ?[D:$i]:
% 0.19/0.49            ( ( ![E:$i]:
% 0.19/0.49                ( ( m1_subset_1 @ E @ A ) =>
% 0.19/0.49                  ( ![F:$i]:
% 0.19/0.49                    ( ( m1_subset_1 @ F @ B ) =>
% 0.19/0.49                      ( ![G:$i]:
% 0.19/0.49                        ( ( m1_subset_1 @ G @ C ) =>
% 0.19/0.49                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.19/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((X6) = (k1_xboole_0))
% 0.19/0.49          | ((X7) = (k1_xboole_0))
% 0.19/0.49          | ((X8)
% 0.19/0.49              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.19/0.49                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.49          | ((X9) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((X6) = (k1_xboole_0))
% 0.19/0.49          | ((X7) = (k1_xboole_0))
% 0.19/0.49          | ((X8)
% 0.19/0.49              = (k4_tarski @ 
% 0.19/0.49                 (k4_tarski @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.19/0.49                  (sk_F @ X8 @ X9 @ X7 @ X6)) @ 
% 0.19/0.49                 (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.49          | ((X9) = (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_E_1)
% 0.19/0.49            = (k4_tarski @ 
% 0.19/0.49               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49                (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.49  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('20', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((sk_E_1)
% 0.19/0.49         = (k4_tarski @ 
% 0.19/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (((sk_E_1)
% 0.19/0.49         = (k4_tarski @ 
% 0.19/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((X6) = (k1_xboole_0))
% 0.19/0.49          | ((X7) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.49          | ((X9) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((sk_C) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X20 @ sk_B)
% 0.19/0.49          | ((sk_E_1) != (k3_mcart_1 @ X21 @ X20 @ X22))
% 0.19/0.49          | ((sk_D) = (X22))
% 0.19/0.49          | ~ (m1_subset_1 @ X22 @ sk_C)
% 0.19/0.49          | ~ (m1_subset_1 @ X21 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X20 @ sk_B)
% 0.19/0.49          | ((sk_E_1) != (k4_tarski @ (k4_tarski @ X21 @ X20) @ X22))
% 0.19/0.49          | ((sk_D) = (X22))
% 0.19/0.49          | ~ (m1_subset_1 @ X22 @ sk_C)
% 0.19/0.49          | ~ (m1_subset_1 @ X21 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.19/0.49          | ((sk_D) = (X1))
% 0.19/0.49          | ((sk_E_1)
% 0.19/0.49              != (k4_tarski @ 
% 0.19/0.49                  (k4_tarski @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      ((((sk_E_1) != (sk_E_1))
% 0.19/0.49        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((X6) = (k1_xboole_0))
% 0.19/0.49          | ((X7) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.49          | ((X9) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((((sk_C) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('41', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['38', '39', '40', '41'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((X6) = (k1_xboole_0))
% 0.19/0.49          | ((X7) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.49          | ((X9) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      ((((sk_C) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      ((((sk_E_1) != (sk_E_1))
% 0.19/0.49        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['35', '42', '49'])).
% 0.19/0.49  thf('51', plain, (((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (((sk_E_1)
% 0.19/0.49         = (k4_tarski @ 
% 0.19/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.49            sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '51'])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (('#_fresh_sk2' @ (k4_tarski @ (k4_tarski @ X11 @ X14) @ X15)) = (X14))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (![X0 : $i]: (('#_fresh_sk2' @ (k4_tarski @ sk_E_1 @ X0)) = (sk_D))),
% 0.19/0.49      inference('sup+', [status(thm)], ['52', '53'])).
% 0.19/0.49  thf('55', plain, (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '54'])).
% 0.19/0.49  thf('56', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('57', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
