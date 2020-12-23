%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hms2ps2xP3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  576 (1187 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

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

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_G )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['3'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('6',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_G ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('8',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_G ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_E @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('13',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ X0 ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('15',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X3 ) @ X2 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ X1 ) @ X0 ) @ X4 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('18',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ X3 @ X2 @ X5 ) @ ( k4_zfmisc_1 @ sk_E @ X1 @ X0 @ X4 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_F )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_F ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('27',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ sk_B ) @ X2 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_F ) @ X0 ) @ X4 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('30',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ sk_B @ X2 @ X5 ) @ ( k4_zfmisc_1 @ X1 @ sk_F @ X0 @ X4 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_H )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X3 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D ) @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_D @ sk_H )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C @ sk_G ),
    inference('sat_resolution*',[status(thm)],['20','32','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_G ) @ X2 ) ) ),
    inference(simpl_trail,[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ sk_G ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_zfmisc_1 @ X5 @ X4 @ sk_C @ X3 ) @ ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hms2ps2xP3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 74 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(t64_mcart_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.50     ( ( ~( r1_xboole_0 @
% 0.20/0.50            ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.20/0.50       ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.20/0.50         ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.50        ( ( ~( r1_xboole_0 @
% 0.20/0.50               ( k4_zfmisc_1 @ A @ B @ C @ D ) @ 
% 0.20/0.50               ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.20/0.50          ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.20/0.50            ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t64_mcart_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.50          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t53_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_E)
% 0.20/0.50        | (r1_xboole_0 @ sk_B @ sk_F)
% 0.20/0.50        | (r1_xboole_0 @ sk_C @ sk_G)
% 0.20/0.50        | (r1_xboole_0 @ sk_D @ sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_C @ sk_G)) <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(t127_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.50       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_G)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C) @ X3) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_G) @ X2)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_E)) <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_E @ X0)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X3) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ X0) @ X2)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50          (r1_xboole_0 @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X3) @ X2) @ X5) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ X1) @ X0) @ X4)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ X3 @ X2 @ X5) @ 
% 0.20/0.50           (k4_zfmisc_1 @ sk_E @ X1 @ X0 @ X4)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.50          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, (~ ((r1_xboole_0 @ sk_A @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_B @ sk_F)) <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_F)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B) @ X3) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_F) @ X2)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50          (r1_xboole_0 @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ sk_B) @ X2) @ X5) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_F) @ X0) @ X4)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k4_zfmisc_1 @ X3 @ sk_B @ X2 @ X5) @ 
% 0.20/0.50           (k4_zfmisc_1 @ X1 @ sk_F @ X0 @ X4)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.50          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, (~ ((r1_xboole_0 @ sk_B @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_D @ sk_H)) <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_H)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) @ 
% 0.20/0.50           (k2_zfmisc_1 @ X3 @ sk_H)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['34', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50          (r1_xboole_0 @ (k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D) @ 
% 0.20/0.50           (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['33', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.50          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, (~ ((r1_xboole_0 @ sk_D @ sk_H))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_C @ sk_G)) | ((r1_xboole_0 @ sk_D @ sk_H)) | 
% 0.20/0.50       ((r1_xboole_0 @ sk_B @ sk_F)) | ((r1_xboole_0 @ sk_A @ sk_E))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('43', plain, (((r1_xboole_0 @ sk_C @ sk_G))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['20', '32', '41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C) @ X3) @ 
% 0.20/0.50          (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_G) @ X2))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['8', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (r1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) @ 
% 0.20/0.50          (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ sk_G) @ X3))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (r1_xboole_0 @ (k4_zfmisc_1 @ X5 @ X4 @ sk_C @ X3) @ 
% 0.20/0.50          (k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '45'])).
% 0.20/0.50  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
