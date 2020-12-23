%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Xpz3a54yy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 280 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ( k7_relat_1 @ o_0_0_xboole_0 @ sk_A )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( ( k7_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('11',plain,
    ( ( ( k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( ( k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('14',plain,
    ( ( k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X4 @ X2 ) @ X3 )
        = ( k7_relat_1 @ X4 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ o_0_0_xboole_0 ) @ X0 )
        = ( k7_relat_1 @ X1 @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
        = ( k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Xpz3a54yy
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 14 iterations in 0.010s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(t111_relat_1, conjecture,
% 0.20/0.47    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.20/0.47  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.47  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('3', plain, (((k7_relat_1 @ o_0_0_xboole_0 @ sk_A) != (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.47  thf(cc1_relat_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.47  thf('4', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.47  thf('5', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.47  thf(t60_relat_1, axiom,
% 0.20/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.47  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('9', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.47  thf(t98_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.47        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.47        | ((k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0) = (o_0_0_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '11'])).
% 0.20/0.47  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.20/0.47  thf('13', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('17', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(t102_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.47          | ~ (v1_relat_1 @ X4)
% 0.20/0.47          | ((k7_relat_1 @ (k7_relat_1 @ X4 @ X2) @ X3)
% 0.20/0.47              = (k7_relat_1 @ X4 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k7_relat_1 @ (k7_relat_1 @ X1 @ o_0_0_xboole_0) @ X0)
% 0.20/0.47            = (k7_relat_1 @ X1 @ o_0_0_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k7_relat_1 @ o_0_0_xboole_0 @ X0)
% 0.20/0.47            = (k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['14', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((k7_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.47          | ((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '22'])).
% 0.20/0.47  thf('24', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]: ((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '25'])).
% 0.20/0.47  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
