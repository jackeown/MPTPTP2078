%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k1sH9Tn6BA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  282 ( 603 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t4_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
            & ( r1_xboole_0 @ A @ B ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ B )
            & ! [C: $i] :
                ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_xboole_0])).

thf('0',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('14',plain,
    ( ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ! [X7: $i] :
          ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,
    ( ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ! [X7: $i] :
          ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','15','16','17','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k1sH9Tn6BA
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 38 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(t4_xboole_0, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47               ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47          ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47               ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X7 : $i]:
% 0.20/0.47         ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.20/0.47          | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))) | 
% 0.20/0.47       ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X7 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ sk_A @ sk_B_1)
% 0.20/0.47          | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf(d7_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.47         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.20/0.47        | ~ (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.47         <= (((r1_xboole_0 @ sk_A @ sk_B_1)) & 
% 0.20/0.47             ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.47  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (~ ((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       ~ ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (~ ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1))) | 
% 0.20/0.47       ~ (![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       (![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (~ ((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf(l13_xboole_0, axiom,
% 0.20/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X3 @ X5) | ((k3_xboole_0 @ X3 @ X5) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B_1)))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 0.20/0.47         <= ((![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       ~ (![X7 : $i]: ~ (r2_hidden @ X7 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ($false),
% 0.20/0.47      inference('sat_resolution*', [status(thm)],
% 0.20/0.47                ['1', '12', '15', '16', '17', '27'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
