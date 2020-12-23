%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KROvj9ev81

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 208 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  503 (2301 expanded)
%              Number of equality atoms :   12 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['9','16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['9','16','17','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['9','16','17','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('41',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['19','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KROvj9ev81
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 99 iterations in 0.072s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(t107_xboole_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.53       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.53          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.53        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.53        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.53        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf(l98_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k5_xboole_0 @ A @ B ) =
% 0.20/0.53       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.20/0.53  thf(t106_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.20/0.53          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X2 @ X4)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.20/0.53          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('18', plain, (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['9', '16', '17'])).
% 0.20/0.53  thf('19', plain, (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('22', plain, (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['9', '16', '17', '21'])).
% 0.20/0.53  thf('23', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['20', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.53        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf(t83_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.53       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('29', plain, (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['9', '16', '17', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.20/0.53  thf(t44_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.20/0.53       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.20/0.53          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ sk_A @ X0)
% 0.20/0.53          | (r1_tarski @ sk_A @ 
% 0.20/0.53             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((r1_tarski @ sk_A @ 
% 0.20/0.53        (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.20/0.53         (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.20/0.53  thf(t98_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X16 @ X17)
% 0.20/0.53           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.53           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((r1_tarski @ sk_A @ 
% 0.20/0.53        (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.20/0.53         (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.20/0.53          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((r1_tarski @ sk_A @ 
% 0.20/0.53        (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.20/0.53         (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf(t43_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.53          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((r1_tarski @ (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.20/0.53        (k5_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.20/0.53  thf('43', plain, ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, ($false), inference('demod', [status(thm)], ['19', '43'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
