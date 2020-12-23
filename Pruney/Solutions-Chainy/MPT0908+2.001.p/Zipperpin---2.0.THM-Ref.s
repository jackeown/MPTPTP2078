%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0GakUnBv3Z

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 144 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  753 (2591 expanded)
%              Number of equality atoms :  122 ( 416 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('10',plain,(
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

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X10: $i,X12: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X10 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = sk_F ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = sk_F )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( sk_F != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['1','20'])).

thf('22',plain,
    ( $false
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('34',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = sk_E ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_E ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( sk_E != sk_E )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_E ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('46',plain,(
    ! [X10: $i,X12: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X10 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_mcart_1 @ sk_D )
    = sk_G ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = sk_G )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( sk_G != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_G ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_F ),
    inference('sat_resolution*',[status(thm)],['38','56','57'])).

thf('59',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['22','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0GakUnBv3Z
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:56 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 32 iterations in 0.018s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t68_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48            ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.48              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.48                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.48                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.48                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48               ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48               ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.48                 ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.48                        ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.48                        ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.48                   ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t68_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F))
% 0.21/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F)))
% 0.21/0.48         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
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
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.48  thf('9', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.48  thf(t7_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]: ((k1_mcart_1 @ (k4_tarski @ X10 @ X11)) = (X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, (((k1_mcart_1 @ sk_D) = (k4_tarski @ sk_E @ sk_F))),
% 0.21/0.48      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X10 : $i, X12 : $i]: ((k2_mcart_1 @ (k4_tarski @ X10 @ X12)) = (X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('15', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_D)) = (sk_F))),
% 0.21/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '15'])).
% 0.21/0.48  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain, (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((sk_F) != (sk_F)))
% 0.21/0.48         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (($false) <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k5_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k5_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.48  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.48  thf('32', plain, (((k1_mcart_1 @ sk_D) = (k4_tarski @ sk_E @ sk_F))),
% 0.21/0.48      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]: ((k1_mcart_1 @ (k4_tarski @ X10 @ X11)) = (X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('34', plain, (((k1_mcart_1 @ (k1_mcart_1 @ sk_D)) = (sk_E))),
% 0.21/0.48      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E)))
% 0.21/0.48         <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((((sk_E) != (sk_E)))
% 0.21/0.48         <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X6) = (k1_xboole_0))
% 0.21/0.48          | ((X7) = (k1_xboole_0))
% 0.21/0.48          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.48          | ((X9) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.48  thf('44', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.48           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X10 : $i, X12 : $i]: ((k2_mcart_1 @ (k4_tarski @ X10 @ X12)) = (X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain, (((k2_mcart_1 @ sk_D) = (sk_G))),
% 0.21/0.48      inference('sup+', [status(thm)], ['44', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['43', '48'])).
% 0.21/0.48  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain, (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))
% 0.21/0.48         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((sk_G) != (sk_G)))
% 0.21/0.48         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))) | 
% 0.21/0.48       ~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))) | 
% 0.21/0.48       ~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('58', plain, (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['38', '56', '57'])).
% 0.21/0.48  thf('59', plain, ($false),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['22', '58'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
