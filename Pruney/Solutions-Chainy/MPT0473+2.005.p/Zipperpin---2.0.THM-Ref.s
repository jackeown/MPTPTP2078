%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.brxlmgyMAY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  83 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 ( 665 expanded)
%              Number of equality atoms :   61 ( 154 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
   <= ( ( k2_relat_1 @ sk_A )
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

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('5',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('12',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','20','21'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['8','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','23','24'])).

thf('26',plain,
    ( $false
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ( k2_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','20'])).

thf('28',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.brxlmgyMAY
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 14 iterations in 0.009s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
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
% 0.21/0.47      ((((k2_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.47        | ((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(t64_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.47          | ((X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.47          | ((X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf(t60_relat_1, axiom,
% 0.21/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.47             (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       (((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('22', plain, ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['9', '20', '21'])).
% 0.21/0.47  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['8', '22'])).
% 0.21/0.47  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '23', '24'])).
% 0.21/0.47  thf('26', plain, (($false) <= (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.47  thf('27', plain, (~ (((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['9', '20'])).
% 0.21/0.47  thf('28', plain, ($false),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['26', '27'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
