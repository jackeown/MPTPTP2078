%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rNBThYMqfI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:41 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 131 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  398 ( 896 expanded)
%              Number of equality atoms :   48 (  97 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','8'])).

thf('10',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','8','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['11','13'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_A @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','40'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rNBThYMqfI
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 206 iterations in 0.107s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(t83_xboole_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.37/0.57         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.37/0.57       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.37/0.57         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['3'])).
% 0.37/0.57  thf(t79_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.37/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.37/0.57       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('9', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['2', '8'])).
% 0.37/0.57  thf('10', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['1', '9'])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['3'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['3'])).
% 0.37/0.57  thf('13', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['2', '8', '12'])).
% 0.37/0.57  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['11', '13'])).
% 0.37/0.57  thf(d7_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf(t47_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.37/0.57           = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.57  thf('19', plain, (((k4_xboole_0 @ sk_A @ k1_xboole_0) != (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.37/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.37/0.57           = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.37/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_A) != (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['19', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.37/0.57           = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.37/0.57           = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.37/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.37/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.37/0.57           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.37/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.37/0.57  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['34', '40'])).
% 0.37/0.57  thf(t51_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.57       ( A ) ))).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.57           = (X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.57  thf(t1_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('44', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.57  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain, (((sk_A) != (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['29', '45'])).
% 0.37/0.57  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
