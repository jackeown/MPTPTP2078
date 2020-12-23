%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NgNZExrjXZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 447 expanded)
%              Number of equality atoms :   24 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B_1 )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','8'])).

thf('22',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NgNZExrjXZ
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:12:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 23 iterations in 0.013s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(t83_xboole_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))
% 0.20/0.47        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_B_1) != (sk_A))
% 0.20/0.47        | ~ (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (~ (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))) | 
% 0.20/0.47       ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf(t79_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.20/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 0.20/0.47         <= ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       ~ (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.20/0.47       (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['3', '8', '9'])).
% 0.20/0.47  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.20/0.47  thf(t7_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.47  thf(t4_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.47  thf(t47_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.20/0.47           = (k4_xboole_0 @ X6 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(t3_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('18', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.47  thf('19', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((((k4_xboole_0 @ sk_A @ sk_B_1) != (sk_A)))
% 0.20/0.47         <= (~ (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('21', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['3', '8'])).
% 0.20/0.47  thf('22', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) != (sk_A))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['19', '22'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
