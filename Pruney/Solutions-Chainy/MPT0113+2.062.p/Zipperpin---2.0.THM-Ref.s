%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uP7GClOjp2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:36 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 163 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  522 (1144 expanded)
%              Number of equality atoms :   40 (  80 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t80_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t80_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('49',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['19','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uP7GClOjp2
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 447 iterations in 0.112s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(t106_xboole_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.56          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(t79_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.37/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(l32_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X2 : $i, X4 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf(t84_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.37/0.56          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X18 @ X19)
% 0.37/0.56          | ~ (r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.56          | ~ (r1_xboole_0 @ X18 @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.56          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.37/0.56          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.56  thf('10', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.37/0.56          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.56  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('16', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('18', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.37/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.56  thf(t80_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X12 @ X13)
% 0.37/0.56          | (r1_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t80_xboole_1])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.37/0.56          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf(t83_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.56  thf(t48_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('30', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(t47_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.37/0.56           = (k4_xboole_0 @ X5 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('33', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.56  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.37/0.56           = (k4_xboole_0 @ X5 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.37/0.56          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.56        | (r1_tarski @ sk_A @ 
% 0.37/0.56           (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.37/0.56         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.56  thf('50', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['44', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X2 : $i, X4 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf('52', plain, (((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['53', '54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.37/0.56           = (k4_xboole_0 @ X5 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X1 @ X0)
% 0.37/0.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['52', '57'])).
% 0.37/0.56  thf('59', plain, (((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('60', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['58', '59'])).
% 0.37/0.56  thf('61', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.56  thf('65', plain, ($false), inference('demod', [status(thm)], ['19', '64'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
