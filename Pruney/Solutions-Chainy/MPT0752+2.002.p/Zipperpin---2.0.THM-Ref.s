%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wXN9afLxMe

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 317 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('4',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( v5_ordinal1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf('14',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
   <= ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','11','16','17'])).

thf('19',plain,(
    ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['19','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wXN9afLxMe
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 25 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.22/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(t45_ordinal1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.22/0.47       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.22/0.47          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.22/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.47        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.22/0.47         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.47  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.47  thf(cc1_funct_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.22/0.47  thf('3', plain, (![X7 : $i]: ((v1_funct_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.47  thf('4', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      ((~ (v1_funct_1 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('6', plain, (((v1_funct_1 @ k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf(cc1_relat_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.47  thf('7', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.47  thf('11', plain, (((v1_relat_1 @ k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.47  thf(cc4_ordinal1, axiom,
% 0.22/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.22/0.47  thf('13', plain, (![X8 : $i]: ((v5_ordinal1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.22/0.47  thf('14', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)) <= (~ ((v5_ordinal1 @ k1_xboole_0)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('16', plain, (((v5_ordinal1 @ k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)) | 
% 0.22/0.47       ~ ((v5_ordinal1 @ k1_xboole_0)) | ~ ((v1_relat_1 @ k1_xboole_0)) | 
% 0.22/0.47       ~ ((v1_funct_1 @ k1_xboole_0))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('18', plain, (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['6', '11', '16', '17'])).
% 0.22/0.47  thf('19', plain, (~ (v5_relat_1 @ k1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.22/0.47  thf('20', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.47  thf(t60_relat_1, axiom,
% 0.22/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.47  thf(d19_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i]:
% 0.22/0.47         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.22/0.47          | (v5_relat_1 @ X5 @ X6)
% 0.22/0.47          | ~ (v1_relat_1 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.47          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf(t4_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.47  thf(t37_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.47  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['23', '27'])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['20', '28'])).
% 0.22/0.47  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.47  thf('31', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.47  thf('32', plain, ($false), inference('demod', [status(thm)], ['19', '31'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
