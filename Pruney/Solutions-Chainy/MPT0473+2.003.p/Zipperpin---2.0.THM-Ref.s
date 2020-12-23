%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bDt7Hmqiby

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 449 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('5',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('19',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bDt7Hmqiby
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 39 iterations in 0.025s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(t65_relat_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( v1_relat_1 @ A ) =>
% 0.19/0.48          ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48            ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t65_relat_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) != (k1_xboole_0))
% 0.19/0.48        | ((k1_relat_1 @ sk_A) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.48       ~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.19/0.48         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf(fc8_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X1 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (k1_relat_1 @ X1))
% 0.19/0.48          | ~ (v1_relat_1 @ X1)
% 0.19/0.48          | (v1_xboole_0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48         | (v1_xboole_0 @ sk_A)
% 0.19/0.48         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_A)) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.48  thf(l13_xboole_0, axiom,
% 0.19/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.48             (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf(t60_relat_1, axiom,
% 0.19/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.48             (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.48       ~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.48       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.19/0.48         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf(fc9_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X2 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (k2_relat_1 @ X2))
% 0.19/0.48          | ~ (v1_relat_1 @ X2)
% 0.19/0.48          | (v1_xboole_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48         | (v1_xboole_0 @ sk_A)
% 0.19/0.48         | ~ (v1_relat_1 @ sk_A))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_A)) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.48             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.48         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.48             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.48       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  thf('30', plain, ($false),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '29'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
