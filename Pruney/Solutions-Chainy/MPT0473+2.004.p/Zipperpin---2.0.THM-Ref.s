%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BH0PLl0UXn

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  282 ( 495 expanded)
%              Number of equality atoms :   54 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t65_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
        <=> ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_relat_1])).

thf('0',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('2',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_A_1 ) )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 ) )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A_1 )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A_1 )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_A_1 ) )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['2','5'])).

thf('26',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A_1 )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A_1 )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BH0PLl0UXn
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(t65_relat_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ A ) =>
% 0.21/0.48          ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48            ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t65_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) != (k1_xboole_0))
% 0.21/0.48        | ((k1_relat_1 @ sk_A_1) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (~ (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) | 
% 0.21/0.48       ~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.21/0.48  thf('2', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.48  thf('3', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.48  thf(l13_xboole_0, axiom,
% 0.21/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('5', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))
% 0.21/0.48        | ((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf(fc8_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (k1_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.48         | (v1_xboole_0 @ sk_A_1)
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A_1)))
% 0.21/0.48         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A_1)))
% 0.21/0.48         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A_1)) <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((sk_A_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) & 
% 0.21/0.48             (((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) & 
% 0.21/0.48             (((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) | 
% 0.21/0.48       ~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) | 
% 0.21/0.48       (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf(fc9_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X2 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (k2_relat_1 @ X2))
% 0.21/0.48          | ~ (v1_relat_1 @ X2)
% 0.21/0.48          | (v1_xboole_0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.48         | (v1_xboole_0 @ sk_A_1)
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A_1)))
% 0.21/0.48         <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('26', plain, ((v1_relat_1 @ sk_A_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A_1)) <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_A_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_A_1) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0))) & 
% 0.21/0.48             (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0))) & 
% 0.21/0.48             (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (~ (((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) | 
% 0.21/0.48       (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.48  thf('35', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '34'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
