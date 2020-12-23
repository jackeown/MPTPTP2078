%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hqesOBFUJK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  527 (1094 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ~ ( r1_xboole_0 @ A @ E )
        & ~ ( r1_xboole_0 @ B @ F )
        & ~ ( r1_xboole_0 @ C @ G )
        & ~ ( r1_xboole_0 @ D @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ~ ( r1_xboole_0 @ A @ E )
          & ~ ( r1_xboole_0 @ B @ F )
          & ~ ( r1_xboole_0 @ C @ G )
          & ~ ( r1_xboole_0 @ D @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_mcart_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['1'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('4',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_E @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t52_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ~ ( r1_xboole_0 @ A @ D )
        & ~ ( r1_xboole_0 @ B @ E )
        & ~ ( r1_xboole_0 @ C @ F ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ ( k3_zfmisc_1 @ X4 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X5 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_mcart_1])).

thf('6',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X5 @ X4 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ X0 ) @ X3 @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('9',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ X1 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ sk_E @ X0 @ X3 @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_H )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['1'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X9 )
      | ( r1_xboole_0 @ ( k3_zfmisc_1 @ X4 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X5 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_mcart_1])).

thf('14',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_D ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D ) @ ( k3_zfmisc_1 @ X4 @ X3 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D ) @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_G )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['1'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X8 )
      | ( r1_xboole_0 @ ( k3_zfmisc_1 @ X4 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X5 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_mcart_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ sk_C @ X2 ) @ ( k3_zfmisc_1 @ X1 @ sk_G @ X0 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 ) @ ( k3_zfmisc_1 @ X4 @ sk_G @ X3 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X5 @ X4 @ sk_C @ X3 ) @ ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_F )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('30',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ ( k3_zfmisc_1 @ X4 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X5 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_mcart_1])).

thf('32',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ X5 @ X4 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_F ) @ X3 @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 @ X13 )
      = ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('35',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X1 @ sk_B @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X0 @ sk_F @ X3 @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_E ),
    inference('sat_resolution*',[status(thm)],['18','27','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ X1 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ sk_E @ X0 @ X3 @ X2 ) ) ),
    inference(simpl_trail,[status(thm)],['9','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hqesOBFUJK
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 81 iterations in 0.101s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.55  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(t64_mcart_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.37/0.55     ( ( ~( r1_xboole_0 @
% 0.37/0.55            ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.37/0.55       ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.37/0.55         ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.37/0.55        ( ( ~( r1_xboole_0 @
% 0.37/0.55               ( k4_zfmisc_1 @ A @ B @ C @ D ) @ 
% 0.37/0.55               ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.37/0.55          ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.37/0.55            ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t64_mcart_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.55          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_A @ sk_E)
% 0.37/0.55        | (r1_xboole_0 @ sk_B @ sk_F)
% 0.37/0.55        | (r1_xboole_0 @ sk_C @ sk_G)
% 0.37/0.55        | (r1_xboole_0 @ sk_D @ sk_H))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_A @ sk_E)) <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf(t127_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.37/0.55       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_E @ X0)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(t52_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.55     ( ( ~( r1_xboole_0 @
% 0.37/0.55            ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) ) =>
% 0.37/0.55       ( ( ~( r1_xboole_0 @ A @ D ) ) & ( ~( r1_xboole_0 @ B @ E ) ) & 
% 0.37/0.55         ( ~( r1_xboole_0 @ C @ F ) ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ X4 @ X5)
% 0.37/0.55          | (r1_xboole_0 @ (k3_zfmisc_1 @ X4 @ X6 @ X7) @ 
% 0.37/0.55             (k3_zfmisc_1 @ X5 @ X8 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_mcart_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X5 @ X4) @ 
% 0.37/0.55           (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ X0) @ X3 @ X2)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf(t54_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.37/0.55       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ X1 @ X5 @ X4) @ 
% 0.37/0.55           (k4_zfmisc_1 @ sk_E @ X0 @ X3 @ X2)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.37/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_D @ sk_H)) <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ X7 @ X9)
% 0.37/0.55          | (r1_xboole_0 @ (k3_zfmisc_1 @ X4 @ X6 @ X7) @ 
% 0.37/0.55             (k3_zfmisc_1 @ X5 @ X8 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_mcart_1])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ sk_D) @ 
% 0.37/0.55           (k3_zfmisc_1 @ X1 @ X0 @ sk_H)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) @ 
% 0.37/0.55           (k3_zfmisc_1 @ X4 @ X3 @ sk_H)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D) @ 
% 0.37/0.55           (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['10', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.55          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('18', plain, (~ ((r1_xboole_0 @ sk_D @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_C @ sk_G)) <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ X6 @ X8)
% 0.37/0.55          | (r1_xboole_0 @ (k3_zfmisc_1 @ X4 @ X6 @ X7) @ 
% 0.37/0.55             (k3_zfmisc_1 @ X5 @ X8 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_mcart_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k3_zfmisc_1 @ X3 @ sk_C @ X2) @ 
% 0.37/0.55           (k3_zfmisc_1 @ X1 @ sk_G @ X0)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) @ 
% 0.37/0.55           (k3_zfmisc_1 @ X4 @ sk_G @ X3)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ X5 @ X4 @ sk_C @ X3) @ 
% 0.37/0.55           (k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['19', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.55          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('27', plain, (~ ((r1_xboole_0 @ sk_C @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_B @ sk_F)) <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.37/0.55          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_F)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ X4 @ X5)
% 0.37/0.55          | (r1_xboole_0 @ (k3_zfmisc_1 @ X4 @ X6 @ X7) @ 
% 0.37/0.55             (k3_zfmisc_1 @ X5 @ X8 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_mcart_1])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k3_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B) @ X5 @ X4) @ 
% 0.37/0.55           (k3_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_F) @ X3 @ X2)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12 @ X13)
% 0.37/0.55           = (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55          (r1_xboole_0 @ (k4_zfmisc_1 @ X1 @ sk_B @ X5 @ X4) @ 
% 0.37/0.55           (k4_zfmisc_1 @ X0 @ sk_F @ X3 @ X2)))
% 0.37/0.55         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.55          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('37', plain, (~ ((r1_xboole_0 @ sk_B @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_A @ sk_E)) | ((r1_xboole_0 @ sk_B @ sk_F)) | 
% 0.37/0.55       ((r1_xboole_0 @ sk_C @ sk_G)) | ((r1_xboole_0 @ sk_D @ sk_H))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('39', plain, (((r1_xboole_0 @ sk_A @ sk_E))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['18', '27', '37', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ X1 @ X5 @ X4) @ 
% 0.37/0.55          (k4_zfmisc_1 @ sk_E @ X0 @ X3 @ X2))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 0.37/0.55  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
