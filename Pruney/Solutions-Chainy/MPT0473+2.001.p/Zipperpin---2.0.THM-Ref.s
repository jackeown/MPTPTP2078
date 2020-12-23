%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DmrjKhSd5S

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 493 expanded)
%              Number of equality atoms :   53 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
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

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
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

thf('22',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('23',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DmrjKhSd5S
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 28 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(t65_relat_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ A ) =>
% 0.21/0.47          ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47            ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t65_relat_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) != (k1_xboole_0))
% 0.21/0.47        | ((k1_relat_1 @ sk_A) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.47        | ((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(fc8_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k1_relat_1 @ X3))
% 0.21/0.47          | ~ (v1_relat_1 @ X3)
% 0.21/0.47          | (v1_xboole_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47         | (v1_xboole_0 @ sk_A)
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.47  thf(l13_xboole_0, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf(fc11_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X2 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(fc9_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_relat_1 @ X4))
% 0.21/0.47          | ~ (v1_relat_1 @ X4)
% 0.21/0.47          | (v1_xboole_0 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47         | (v1_xboole_0 @ sk_A)
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf(fc10_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X1 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X1)) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['30', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.47  thf('38', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '37'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
