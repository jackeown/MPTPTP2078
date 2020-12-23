%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F8lPFzksM7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 270 expanded)
%              Number of leaves         :   19 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  493 (1976 expanded)
%              Number of equality atoms :   45 ( 163 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    r1_tarski @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X23 )
      | ( ( k4_xboole_0 @ X21 @ X23 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X23 )
      | ( ( k4_xboole_0 @ X21 @ X23 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != ( k3_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','38'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('54',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['44','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F8lPFzksM7
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:35:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 287 iterations in 0.128s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(t106_xboole_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.54       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.54        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.54          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t28_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.19/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf(t36_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.19/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.54  thf(l32_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X3 : $i, X5 : $i]:
% 0.19/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.54  thf(t49_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.19/0.54       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.19/0.54           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i]:
% 0.19/0.54         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.19/0.54          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.54          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.54  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X3 : $i, X5 : $i]:
% 0.19/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.19/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.54  thf('16', plain, ((r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.19/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X3 : $i, X5 : $i]:
% 0.19/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('18', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.19/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.54  thf('20', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (![X3 : $i, X5 : $i]:
% 0.19/0.54         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.54  thf(t83_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X21 : $i, X23 : $i]:
% 0.19/0.54         ((r1_xboole_0 @ X21 @ X23) | ((k4_xboole_0 @ X21 @ X23) != (X21)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.54        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.54  thf('25', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.54  thf(d7_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.54  thf(t16_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.54       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.19/0.54           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.54  thf(t100_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      (![X8 : $i, X9 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.19/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 0.19/0.54           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.19/0.54              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.19/0.54           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.19/0.54           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.19/0.54              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.19/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.19/0.54           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.19/0.54              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['27', '32'])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.54  thf(t92_xboole_1, axiom,
% 0.19/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.54  thf('35', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.19/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.54          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.19/0.54      inference('demod', [status(thm)], ['11', '36'])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0)),
% 0.19/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.54  thf('39', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.54      inference('sup+', [status(thm)], ['4', '38'])).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('41', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('43', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.19/0.54  thf('44', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.19/0.54      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.19/0.54           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      (![X21 : $i, X23 : $i]:
% 0.19/0.54         ((r1_xboole_0 @ X21 @ X23) | ((k4_xboole_0 @ X21 @ X23) != (X21)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.54  thf('48', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.19/0.54            != (k3_xboole_0 @ X2 @ X1))
% 0.19/0.54          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.54  thf('49', plain,
% 0.19/0.54      ((((sk_A) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.54        | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.54      inference('sup-', [status(thm)], ['45', '48'])).
% 0.19/0.54  thf('50', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.54      inference('sup+', [status(thm)], ['4', '38'])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.19/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.54  thf('52', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.54  thf('53', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.54  thf('54', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.54      inference('demod', [status(thm)], ['49', '52', '53'])).
% 0.19/0.54  thf('55', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.19/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.19/0.54  thf('56', plain, ($false), inference('demod', [status(thm)], ['44', '55'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
