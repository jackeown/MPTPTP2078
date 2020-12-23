%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qjxf9VP0hs

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  78 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 ( 554 expanded)
%              Number of equality atoms :   22 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t66_xboole_1,conjecture,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( ( A != k1_xboole_0 )
            & ( r1_xboole_0 @ A @ A ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ A )
            & ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_xboole_1])).

thf('0',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','10','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','10'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qjxf9VP0hs
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 38 iterations in 0.017s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(t66_xboole_1, conjecture,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.43       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i]:
% 0.20/0.43        ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.43          ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t66_xboole_1])).
% 0.20/0.43  thf('0', plain, (((r1_xboole_0 @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (((r1_xboole_0 @ sk_A @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.20/0.43      inference('split', [status(esa)], ['0'])).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      ((((sk_A) != (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.43      inference('split', [status(esa)], ['2'])).
% 0.20/0.43  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.43  thf('4', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.20/0.43      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.43  thf('5', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.43      inference('split', [status(esa)], ['0'])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      ((~ (r1_xboole_0 @ sk_A @ sk_A)) <= (~ ((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.20/0.43      inference('split', [status(esa)], ['2'])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      ((~ (r1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.20/0.43         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.43      inference('split', [status(esa)], ['0'])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.43         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.20/0.43      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      (((r1_xboole_0 @ sk_A @ sk_A)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (((r1_xboole_0 @ sk_A @ sk_A)) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('split', [status(esa)], ['0'])).
% 0.20/0.43  thf('12', plain, (((r1_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.43      inference('sat_resolution*', [status(thm)], ['3', '10', '11'])).
% 0.20/0.43  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.20/0.43      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.20/0.43  thf(d1_xboole_0, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.44  thf(t3_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.44            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.44          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.44          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((v1_xboole_0 @ X0)
% 0.20/0.44          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.44          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.44      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.44  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.44      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.44  thf(l13_xboole_0, axiom,
% 0.20/0.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.44  thf('21', plain,
% 0.20/0.44      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.44  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.44  thf('23', plain,
% 0.20/0.44      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.44      inference('split', [status(esa)], ['2'])).
% 0.20/0.44  thf('24', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.44      inference('sat_resolution*', [status(thm)], ['3', '10'])).
% 0.20/0.44  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.44      inference('simpl_trail', [status(thm)], ['23', '24'])).
% 0.20/0.44  thf('26', plain, ($false),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
