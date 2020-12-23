%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLMUuY530y

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 259 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  756 (6062 expanded)
%              Number of equality atoms :  120 (1005 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(t68_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ? [E: $i,F: $i,G: $i] :
              ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                    = E )
                  & ( ( k6_mcart_1 @ A @ B @ C @ D )
                    = F )
                  & ( ( k7_mcart_1 @ A @ B @ C @ D )
                    = G ) )
              & ( D
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ~ ( ( A != k1_xboole_0 )
            & ( B != k1_xboole_0 )
            & ( C != k1_xboole_0 )
            & ? [E: $i,F: $i,G: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                      = E )
                    & ( ( k6_mcart_1 @ A @ B @ C @ D )
                      = F )
                    & ( ( k7_mcart_1 @ A @ B @ C @ D )
                      = G ) )
                & ( D
                  = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_mcart_1])).

thf('0',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X10 @ X11 @ X13 @ X12 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k3_zfmisc_1 @ X10 @ X11 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('4',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X9
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X6 @ X7 @ X8 @ X9 ) @ ( k6_mcart_1 @ X6 @ X7 @ X8 @ X9 ) @ ( k7_mcart_1 @ X6 @ X7 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X13 @ X12 )
        = ( k2_mcart_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k3_zfmisc_1 @ X10 @ X11 @ X13 ) )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X1 = X0 )
      | ( ( k3_mcart_1 @ X1 @ X4 @ X5 )
       != ( k3_mcart_1 @ X0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('26',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['25'])).

thf('27',plain,
    ( ( '#_fresh_sk1' @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['25'])).

thf('30',plain,
    ( ( '#_fresh_sk1' @ sk_D )
    = sk_E ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_E
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_E != sk_E )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(demod,[status(thm)],['1','8','31'])).

thf('33',plain,
    ( $false
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X5 = X3 )
      | ( ( k3_mcart_1 @ X1 @ X4 @ X5 )
       != ( k3_mcart_1 @ X0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('36',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk3' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X5 ) ),
    inference(inj_rec,[status(thm)],['35'])).

thf('37',plain,
    ( ( '#_fresh_sk3' @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk3' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X5 ) ),
    inference(inj_rec,[status(thm)],['35'])).

thf('40',plain,
    ( ( '#_fresh_sk3' @ sk_D )
    = sk_G ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_G
    = ( k2_mcart_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('43',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ( k2_mcart_1 @ sk_D )
     != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_G != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_G ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4 = X2 )
      | ( ( k3_mcart_1 @ X1 @ X4 @ X5 )
       != ( k3_mcart_1 @ X0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('49',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X4 ) ),
    inference(inj_rec,[status(thm)],['48'])).

thf('50',plain,
    ( ( '#_fresh_sk2' @ sk_D )
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X1 @ X4 @ X5 ) )
      = X4 ) ),
    inference(inj_rec,[status(thm)],['48'])).

thf('53',plain,
    ( ( '#_fresh_sk2' @ sk_D )
    = sk_F ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_F
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( sk_F != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_F ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['46','57','58'])).

thf('60',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLMUuY530y
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 38 iterations in 0.018s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.49  thf('#_fresh_sk3_type', type, '#_fresh_sk3': $i > $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.49  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.22/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.22/0.49  thf(t68_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49            ( ?[E:$i,F:$i,G:$i]:
% 0.22/0.49              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.22/0.49                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.22/0.49                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.22/0.49                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49               ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49               ( ?[E:$i,F:$i,G:$i]:
% 0.22/0.49                 ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.22/0.49                        ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.22/0.49                        ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.22/0.49                   ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t68_mcart_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E))
% 0.22/0.49        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F))
% 0.22/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E)))
% 0.22/0.49         <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
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
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         (((X10) = (k1_xboole_0))
% 0.22/0.49          | ((X11) = (k1_xboole_0))
% 0.22/0.49          | ((k5_mcart_1 @ X10 @ X11 @ X13 @ X12)
% 0.22/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ X12)))
% 0.22/0.49          | ~ (m1_subset_1 @ X12 @ (k3_zfmisc_1 @ X10 @ X11 @ X13))
% 0.22/0.49          | ((X13) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.49            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7'])).
% 0.22/0.49  thf('9', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t48_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                 ( ( D ) =
% 0.22/0.49                   ( k3_mcart_1 @
% 0.22/0.49                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.49                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.49                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X6) = (k1_xboole_0))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | ((X9)
% 0.22/0.49              = (k3_mcart_1 @ (k5_mcart_1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.22/0.49                 (k6_mcart_1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.22/0.49                 (k7_mcart_1 @ X6 @ X7 @ X8 @ X9)))
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X6 @ X7 @ X8))
% 0.22/0.49          | ((X8) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_D)
% 0.22/0.49            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.22/0.49               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.22/0.49               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7'])).
% 0.22/0.49  thf('13', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         (((X10) = (k1_xboole_0))
% 0.22/0.49          | ((X11) = (k1_xboole_0))
% 0.22/0.49          | ((k7_mcart_1 @ X10 @ X11 @ X13 @ X12) = (k2_mcart_1 @ X12))
% 0.22/0.49          | ~ (m1_subset_1 @ X12 @ (k3_zfmisc_1 @ X10 @ X11 @ X13))
% 0.22/0.49          | ((X13) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_D)
% 0.22/0.49            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12', '19'])).
% 0.22/0.49  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.49  thf(t28_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.22/0.49       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (((X1) = (X0))
% 0.22/0.49          | ((k3_mcart_1 @ X1 @ X4 @ X5) != (k3_mcart_1 @ X0 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk1' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X1))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((('#_fresh_sk1' @ sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['24', '26'])).
% 0.22/0.49  thf('28', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk1' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X1))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['25'])).
% 0.22/0.49  thf('30', plain, ((('#_fresh_sk1' @ sk_D) = (sk_E))),
% 0.22/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, (((sk_E) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('demod', [status(thm)], ['27', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((((sk_E) != (sk_E)))
% 0.22/0.49         <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '8', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (($false) <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (((X5) = (X3))
% 0.22/0.49          | ((k3_mcart_1 @ X1 @ X4 @ X5) != (k3_mcart_1 @ X0 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk3' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X5))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['35'])).
% 0.22/0.49  thf('37', plain, ((('#_fresh_sk3' @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('sup+', [status(thm)], ['34', '36'])).
% 0.22/0.49  thf('38', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk3' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X5))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['35'])).
% 0.22/0.49  thf('40', plain, ((('#_fresh_sk3' @ sk_D) = (sk_G))),
% 0.22/0.49      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain, (((sk_G) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))
% 0.22/0.49         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((((k2_mcart_1 @ sk_D) != (sk_G)))
% 0.22/0.49         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      ((((sk_G) != (sk_G)))
% 0.22/0.49         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.22/0.49  thf('46', plain, ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (((X4) = (X2))
% 0.22/0.49          | ((k3_mcart_1 @ X1 @ X4 @ X5) != (k3_mcart_1 @ X0 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk2' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X4))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['48'])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      ((('#_fresh_sk2' @ sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('sup+', [status(thm)], ['47', '49'])).
% 0.22/0.49  thf('51', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (('#_fresh_sk2' @ (k3_mcart_1 @ X1 @ X4 @ X5)) = (X4))),
% 0.22/0.49      inference('inj_rec', [status(thm)], ['48'])).
% 0.22/0.49  thf('53', plain, ((('#_fresh_sk2' @ sk_D) = (sk_F))),
% 0.22/0.49      inference('sup+', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, (((sk_F) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['50', '53'])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F)))
% 0.22/0.49         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      ((((sk_F) != (sk_F)))
% 0.22/0.49         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.49  thf('57', plain, ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))) | 
% 0.22/0.49       ~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))) | 
% 0.22/0.49       ~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('59', plain, (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['46', '57', '58'])).
% 0.22/0.49  thf('60', plain, ($false),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['33', '59'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
