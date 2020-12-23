%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OICp7ThaTQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:33 EST 2020

% Result     : Theorem 5.31s
% Output     : Refutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 (1048 expanded)
%              Number of equality atoms :   48 ( 107 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['40','47','48'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['39','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OICp7ThaTQ
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:02 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.31/5.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.31/5.51  % Solved by: fo/fo7.sh
% 5.31/5.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.31/5.51  % done 3859 iterations in 5.041s
% 5.31/5.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.31/5.51  % SZS output start Refutation
% 5.31/5.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.31/5.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.31/5.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.31/5.51  thf(sk_C_type, type, sk_C: $i).
% 5.31/5.51  thf(sk_B_type, type, sk_B: $i).
% 5.31/5.51  thf(sk_A_type, type, sk_A: $i).
% 5.31/5.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.31/5.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.31/5.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.31/5.51  thf(t106_xboole_1, conjecture,
% 5.31/5.51    (![A:$i,B:$i,C:$i]:
% 5.31/5.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.31/5.51       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 5.31/5.51  thf(zf_stmt_0, negated_conjecture,
% 5.31/5.51    (~( ![A:$i,B:$i,C:$i]:
% 5.31/5.51        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.31/5.51          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 5.31/5.51    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 5.31/5.51  thf('0', plain,
% 5.31/5.51      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 5.31/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.31/5.51  thf('1', plain,
% 5.31/5.51      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 5.31/5.51      inference('split', [status(esa)], ['0'])).
% 5.31/5.51  thf(t79_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.31/5.51  thf('2', plain,
% 5.31/5.51      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 5.31/5.51      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.31/5.51  thf(d7_xboole_0, axiom,
% 5.31/5.51    (![A:$i,B:$i]:
% 5.31/5.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.31/5.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.31/5.51  thf('3', plain,
% 5.31/5.51      (![X2 : $i, X3 : $i]:
% 5.31/5.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.31/5.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.31/5.51  thf('4', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 5.31/5.51      inference('sup-', [status(thm)], ['2', '3'])).
% 5.31/5.51  thf(commutativity_k3_xboole_0, axiom,
% 5.31/5.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.31/5.51  thf('5', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('6', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.31/5.51      inference('demod', [status(thm)], ['4', '5'])).
% 5.31/5.51  thf(t100_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i]:
% 5.31/5.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.31/5.51  thf('7', plain,
% 5.31/5.51      (![X8 : $i, X9 : $i]:
% 5.31/5.51         ((k4_xboole_0 @ X8 @ X9)
% 5.31/5.51           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 5.31/5.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.31/5.51  thf('8', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.31/5.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['6', '7'])).
% 5.31/5.51  thf(t2_boole, axiom,
% 5.31/5.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.31/5.51  thf('9', plain,
% 5.31/5.51      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 5.31/5.51      inference('cnf', [status(esa)], [t2_boole])).
% 5.31/5.51  thf('10', plain,
% 5.31/5.51      (![X8 : $i, X9 : $i]:
% 5.31/5.51         ((k4_xboole_0 @ X8 @ X9)
% 5.31/5.51           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 5.31/5.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.31/5.51  thf('11', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['9', '10'])).
% 5.31/5.51  thf(t3_boole, axiom,
% 5.31/5.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.31/5.51  thf('12', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 5.31/5.51      inference('cnf', [status(esa)], [t3_boole])).
% 5.31/5.51  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['11', '12'])).
% 5.31/5.51  thf('14', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.31/5.51      inference('demod', [status(thm)], ['8', '13'])).
% 5.31/5.51  thf('15', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.31/5.51      inference('demod', [status(thm)], ['4', '5'])).
% 5.31/5.51  thf('16', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 5.31/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.31/5.51  thf(t28_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i]:
% 5.31/5.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.31/5.51  thf('17', plain,
% 5.31/5.51      (![X15 : $i, X16 : $i]:
% 5.31/5.51         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 5.31/5.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.31/5.51  thf('18', plain,
% 5.31/5.51      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 5.31/5.51      inference('sup-', [status(thm)], ['16', '17'])).
% 5.31/5.51  thf(t16_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i,C:$i]:
% 5.31/5.51     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 5.31/5.51       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.31/5.51  thf('19', plain,
% 5.31/5.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 5.31/5.51           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.31/5.51      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.31/5.51  thf('20', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ sk_A @ X0)
% 5.31/5.51           = (k3_xboole_0 @ sk_A @ 
% 5.31/5.51              (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 5.31/5.51      inference('sup+', [status(thm)], ['18', '19'])).
% 5.31/5.51  thf('21', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ sk_A @ 
% 5.31/5.51           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 5.31/5.51           = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['15', '20'])).
% 5.31/5.51  thf('22', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('23', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('24', plain,
% 5.31/5.51      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 5.31/5.51      inference('cnf', [status(esa)], [t2_boole])).
% 5.31/5.51  thf('25', plain,
% 5.31/5.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['23', '24'])).
% 5.31/5.51  thf('26', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ sk_A @ 
% 5.31/5.51           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 5.31/5.51      inference('demod', [status(thm)], ['21', '22', '25'])).
% 5.31/5.51  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['14', '26'])).
% 5.31/5.51  thf('28', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('29', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 5.31/5.51      inference('demod', [status(thm)], ['27', '28'])).
% 5.31/5.51  thf('30', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('31', plain,
% 5.31/5.51      (![X2 : $i, X4 : $i]:
% 5.31/5.51         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.31/5.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.31/5.51  thf('32', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]:
% 5.31/5.51         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('sup-', [status(thm)], ['30', '31'])).
% 5.31/5.51  thf('33', plain,
% 5.31/5.51      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 5.31/5.51      inference('sup-', [status(thm)], ['29', '32'])).
% 5.31/5.51  thf('34', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 5.31/5.51      inference('simplify', [status(thm)], ['33'])).
% 5.31/5.51  thf('35', plain,
% 5.31/5.51      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 5.31/5.51      inference('split', [status(esa)], ['0'])).
% 5.31/5.51  thf('36', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 5.31/5.51      inference('sup-', [status(thm)], ['34', '35'])).
% 5.31/5.51  thf('37', plain,
% 5.31/5.51      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 5.31/5.51      inference('split', [status(esa)], ['0'])).
% 5.31/5.51  thf('38', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 5.31/5.51      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 5.31/5.51  thf('39', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 5.31/5.51      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 5.31/5.51  thf('40', plain,
% 5.31/5.51      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 5.31/5.51      inference('sup-', [status(thm)], ['16', '17'])).
% 5.31/5.51  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 5.31/5.51      inference('demod', [status(thm)], ['27', '28'])).
% 5.31/5.51  thf('42', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf(t50_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i,C:$i]:
% 5.31/5.51     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 5.31/5.51       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 5.31/5.51  thf('43', plain,
% 5.31/5.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 5.31/5.51           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 5.31/5.51              (k3_xboole_0 @ X19 @ X21)))),
% 5.31/5.51      inference('cnf', [status(esa)], [t50_xboole_1])).
% 5.31/5.51  thf('44', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 5.31/5.51           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 5.31/5.51      inference('sup+', [status(thm)], ['42', '43'])).
% 5.31/5.51  thf('45', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 5.31/5.51           = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 5.31/5.51      inference('sup+', [status(thm)], ['41', '44'])).
% 5.31/5.51  thf('46', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 5.31/5.51      inference('cnf', [status(esa)], [t3_boole])).
% 5.31/5.51  thf('47', plain,
% 5.31/5.51      (![X0 : $i]:
% 5.31/5.51         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 5.31/5.51           = (k3_xboole_0 @ sk_A @ X0))),
% 5.31/5.51      inference('demod', [status(thm)], ['45', '46'])).
% 5.31/5.51  thf('48', plain,
% 5.31/5.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.31/5.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.31/5.51  thf('49', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 5.31/5.51      inference('demod', [status(thm)], ['40', '47', '48'])).
% 5.31/5.51  thf(t17_xboole_1, axiom,
% 5.31/5.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.31/5.51  thf('50', plain,
% 5.31/5.51      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.31/5.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.31/5.51  thf('51', plain, ((r1_tarski @ sk_A @ sk_B)),
% 5.31/5.51      inference('sup+', [status(thm)], ['49', '50'])).
% 5.31/5.51  thf('52', plain, ($false), inference('demod', [status(thm)], ['39', '51'])).
% 5.31/5.51  
% 5.31/5.51  % SZS output end Refutation
% 5.31/5.51  
% 5.31/5.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
