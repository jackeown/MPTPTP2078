%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXI8Nv3Aky

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 120 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 ( 950 expanded)
%              Number of equality atoms :   33 (  84 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('9',plain,
    ( ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','23','27'])).

thf('29',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['25','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXI8Nv3Aky
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 494 iterations in 0.170s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(t95_relat_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.63         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i]:
% 0.45/0.63        ( ( v1_relat_1 @ B ) =>
% 0.45/0.63          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.63            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.63        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.63         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.45/0.63       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf(dt_k7_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.63        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(d7_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf(t90_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.45/0.63         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i]:
% 0.45/0.63         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.45/0.63            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.45/0.63          | ~ (v1_relat_1 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.45/0.63         | ~ (v1_relat_1 @ sk_B)))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf(fc8_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.45/0.63       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X15 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ (k1_relat_1 @ X15))
% 0.45/0.63          | ~ (v1_relat_1 @ X15)
% 0.45/0.63          | (v1_xboole_0 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.63         | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.45/0.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.63  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      ((((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.45/0.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (((~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '15'])).
% 0.45/0.63  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf(l13_xboole_0, axiom,
% 0.45/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.45/0.63         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.45/0.63         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.63         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.45/0.63             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.45/0.63       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.63  thf('24', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '23'])).
% 0.45/0.63  thf('25', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.45/0.63         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.45/0.63       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf('28', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '23', '27'])).
% 0.45/0.63  thf('29', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i]:
% 0.45/0.63         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.45/0.63            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.45/0.63          | ~ (v1_relat_1 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i, X2 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.45/0.63        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.63  thf(t60_relat_1, axiom,
% 0.45/0.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.63  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.63  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.63        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.45/0.63  thf('37', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.45/0.63      inference('simplify', [status(thm)], ['36'])).
% 0.45/0.63  thf('38', plain, ($false), inference('demod', [status(thm)], ['25', '37'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
