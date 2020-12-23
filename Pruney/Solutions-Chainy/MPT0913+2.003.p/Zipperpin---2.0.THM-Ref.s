%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7UqzdCatzX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:03 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 118 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  645 (1472 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(t73_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
    <=> ( ( r2_hidden @ A @ D )
        & ( r2_hidden @ B @ E )
        & ( r2_hidden @ C @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
      <=> ( ( r2_hidden @ A @ D )
          & ( r2_hidden @ B @ E )
          & ( r2_hidden @ C @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_mcart_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F )
    | ~ ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F )
   <= ~ ( r2_hidden @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
    | ( r2_hidden @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
   <= ( r2_hidden @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
   <= ( r2_hidden @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_E ) ) )
   <= ( r2_hidden @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
   <= ( r2_hidden @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) )
   <= ( r2_hidden @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E )
      & ( r2_hidden @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E )
      & ( r2_hidden @ sk_C @ sk_F ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['10'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_E )
   <= ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['10'])).

thf('38',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D )
   <= ~ ( r2_hidden @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ sk_C @ sk_F )
    | ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['10'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['14'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','27','38','43','44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7UqzdCatzX
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 246 iterations in 0.117s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.38/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.38/0.57  thf(t73_mcart_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.57     ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 0.38/0.57       ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & ( r2_hidden @ C @ F ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.57        ( ( r2_hidden @
% 0.38/0.57            ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 0.38/0.57          ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & 
% 0.38/0.57            ( r2_hidden @ C @ F ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t73_mcart_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ sk_F)
% 0.38/0.57        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ sk_F)) | 
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ sk_D)
% 0.38/0.57        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf(d3_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.38/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.38/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.57  thf(d3_mcart_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf(t106_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.38/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((r2_hidden @ X2 @ X3)
% 0.38/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.38/0.57          | (r2_hidden @ X0 @ X3))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k3_mcart_1 @ X5 @ X4 @ X3) @ 
% 0.38/0.57             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.38/0.57          | (r2_hidden @ X3 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ sk_F))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((~ (r2_hidden @ sk_C @ sk_F)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ sk_E)
% 0.38/0.57        | ~ (r2_hidden @ sk_A @ sk_D)
% 0.38/0.57        | ~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      ((~ (r2_hidden @ sk_C @ sk_F)) <= (~ ((r2_hidden @ sk_C @ sk_F)))),
% 0.38/0.57      inference('split', [status(esa)], ['10'])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))) | 
% 0.38/0.57       ((r2_hidden @ sk_C @ sk_F))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ sk_D)) <= (((r2_hidden @ sk_A @ sk_D)))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ sk_E)
% 0.38/0.57        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ sk_E)) <= (((r2_hidden @ sk_B @ sk_E)))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.57         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.38/0.57          | ~ (r2_hidden @ X2 @ X4)
% 0.38/0.57          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((![X0 : $i, X1 : $i]:
% 0.38/0.57          (~ (r2_hidden @ X1 @ X0)
% 0.38/0.57           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_E))))
% 0.38/0.57         <= (((r2_hidden @ sk_B @ sk_E)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.38/0.57         <= (((r2_hidden @ sk_A @ sk_D)) & ((r2_hidden @ sk_B @ sk_E)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ sk_F)) <= (((r2_hidden @ sk_C @ sk_F)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.57         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.38/0.57          | ~ (r2_hidden @ X2 @ X4)
% 0.38/0.57          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((![X0 : $i, X1 : $i]:
% 0.38/0.57          (~ (r2_hidden @ X1 @ X0)
% 0.38/0.57           | (r2_hidden @ (k4_tarski @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_F))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ sk_F)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (((r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_E) @ sk_F)))
% 0.38/0.57         <= (((r2_hidden @ sk_A @ sk_D)) & 
% 0.38/0.57             ((r2_hidden @ sk_B @ sk_E)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ sk_F)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.38/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.38/0.57         <= (((r2_hidden @ sk_A @ sk_D)) & 
% 0.38/0.57             ((r2_hidden @ sk_B @ sk_E)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ sk_F)))),
% 0.38/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('split', [status(esa)], ['10'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (~ ((r2_hidden @ sk_A @ sk_D)) | ~ ((r2_hidden @ sk_B @ sk_E)) | 
% 0.38/0.57       ~ ((r2_hidden @ sk_C @ sk_F)) | 
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.38/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ X1)
% 0.38/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.38/0.57          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ X4))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k3_mcart_1 @ X5 @ X4 @ X3) @ 
% 0.38/0.57             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.38/0.57          | (r2_hidden @ (k4_tarski @ X5 @ X4) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((r2_hidden @ X2 @ X3)
% 0.38/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ sk_E))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((~ (r2_hidden @ sk_B @ sk_E)) <= (~ ((r2_hidden @ sk_B @ sk_E)))),
% 0.38/0.57      inference('split', [status(esa)], ['10'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ sk_E)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '33'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ X1)
% 0.38/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ sk_D))
% 0.38/0.57         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      ((~ (r2_hidden @ sk_A @ sk_D)) <= (~ ((r2_hidden @ sk_A @ sk_D)))),
% 0.38/0.57      inference('split', [status(esa)], ['10'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ sk_D)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))) | 
% 0.38/0.57       ~ ((r2_hidden @ sk_A @ sk_D)) | ~ ((r2_hidden @ sk_C @ sk_F)) | 
% 0.38/0.57       ~ ((r2_hidden @ sk_B @ sk_E))),
% 0.38/0.57      inference('split', [status(esa)], ['10'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ sk_D)) | 
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ sk_E)) | 
% 0.38/0.57       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.57         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('47', plain, ($false),
% 0.38/0.57      inference('sat_resolution*', [status(thm)],
% 0.38/0.57                ['1', '12', '27', '38', '43', '44', '45', '46'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
