%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U6IE8EAzu3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:13 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 279 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 != X27 )
      | ( r2_hidden @ X28 @ X29 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X27: $i] :
      ( r2_hidden @ X27 @ ( k1_tarski @ X27 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X17 ) )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U6IE8EAzu3
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.50/1.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.72  % Solved by: fo/fo7.sh
% 1.50/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.72  % done 1712 iterations in 1.242s
% 1.50/1.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.72  % SZS output start Refutation
% 1.50/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.50/1.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.50/1.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.50/1.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.50/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.72  thf(t13_zfmisc_1, conjecture,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.50/1.72         ( k1_tarski @ A ) ) =>
% 1.50/1.72       ( ( A ) = ( B ) ) ))).
% 1.50/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.72    (~( ![A:$i,B:$i]:
% 1.50/1.72        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.50/1.72            ( k1_tarski @ A ) ) =>
% 1.50/1.72          ( ( A ) = ( B ) ) ) )),
% 1.50/1.72    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 1.50/1.72  thf('0', plain,
% 1.50/1.72      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.50/1.72         = (k1_tarski @ sk_A))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf(t98_xboole_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.50/1.72  thf('1', plain,
% 1.50/1.72      (![X25 : $i, X26 : $i]:
% 1.50/1.72         ((k2_xboole_0 @ X25 @ X26)
% 1.50/1.72           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.50/1.72  thf(d1_tarski, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.50/1.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.50/1.72  thf('2', plain,
% 1.50/1.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.50/1.72         (((X28) != (X27))
% 1.50/1.72          | (r2_hidden @ X28 @ X29)
% 1.50/1.72          | ((X29) != (k1_tarski @ X27)))),
% 1.50/1.72      inference('cnf', [status(esa)], [d1_tarski])).
% 1.50/1.72  thf('3', plain, (![X27 : $i]: (r2_hidden @ X27 @ (k1_tarski @ X27))),
% 1.50/1.72      inference('simplify', [status(thm)], ['2'])).
% 1.50/1.72  thf(d5_xboole_0, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.50/1.72       ( ![D:$i]:
% 1.50/1.72         ( ( r2_hidden @ D @ C ) <=>
% 1.50/1.72           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.50/1.72  thf('4', plain,
% 1.50/1.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.50/1.72         (~ (r2_hidden @ X6 @ X7)
% 1.50/1.72          | (r2_hidden @ X6 @ X8)
% 1.50/1.72          | (r2_hidden @ X6 @ X9)
% 1.50/1.72          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.50/1.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.50/1.72  thf('5', plain,
% 1.50/1.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.50/1.72         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 1.50/1.72          | (r2_hidden @ X6 @ X8)
% 1.50/1.72          | ~ (r2_hidden @ X6 @ X7))),
% 1.50/1.72      inference('simplify', [status(thm)], ['4'])).
% 1.50/1.72  thf('6', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         ((r2_hidden @ X0 @ X1)
% 1.50/1.72          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['3', '5'])).
% 1.50/1.72  thf(t1_xboole_0, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.50/1.72       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.50/1.72  thf('7', plain,
% 1.50/1.72      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.50/1.72         ((r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X17))
% 1.50/1.72          | (r2_hidden @ X14 @ X15)
% 1.50/1.72          | ~ (r2_hidden @ X14 @ X17))),
% 1.50/1.72      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.50/1.72  thf('8', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.72         ((r2_hidden @ X1 @ X0)
% 1.50/1.72          | (r2_hidden @ X1 @ X2)
% 1.50/1.72          | (r2_hidden @ X1 @ 
% 1.50/1.72             (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['6', '7'])).
% 1.50/1.72  thf('9', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.50/1.72          | (r2_hidden @ X0 @ X1)
% 1.50/1.72          | (r2_hidden @ X0 @ X1))),
% 1.50/1.72      inference('sup+', [status(thm)], ['1', '8'])).
% 1.50/1.72  thf('10', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         ((r2_hidden @ X0 @ X1)
% 1.50/1.72          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.50/1.72      inference('simplify', [status(thm)], ['9'])).
% 1.50/1.72  thf(t7_xboole_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.50/1.72  thf('11', plain,
% 1.50/1.72      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.50/1.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.50/1.72  thf(d3_tarski, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( r1_tarski @ A @ B ) <=>
% 1.50/1.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.50/1.72  thf('12', plain,
% 1.50/1.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.50/1.72         (~ (r2_hidden @ X2 @ X3)
% 1.50/1.72          | (r2_hidden @ X2 @ X4)
% 1.50/1.72          | ~ (r1_tarski @ X3 @ X4))),
% 1.50/1.72      inference('cnf', [status(esa)], [d3_tarski])).
% 1.50/1.72  thf('13', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.72         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 1.50/1.72      inference('sup-', [status(thm)], ['11', '12'])).
% 1.50/1.72  thf('14', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.50/1.72      inference('clc', [status(thm)], ['10', '13'])).
% 1.50/1.72  thf('15', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 1.50/1.72      inference('sup+', [status(thm)], ['0', '14'])).
% 1.50/1.72  thf('16', plain,
% 1.50/1.72      (![X27 : $i, X29 : $i, X30 : $i]:
% 1.50/1.72         (~ (r2_hidden @ X30 @ X29)
% 1.50/1.72          | ((X30) = (X27))
% 1.50/1.72          | ((X29) != (k1_tarski @ X27)))),
% 1.50/1.72      inference('cnf', [status(esa)], [d1_tarski])).
% 1.50/1.72  thf('17', plain,
% 1.50/1.72      (![X27 : $i, X30 : $i]:
% 1.50/1.72         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 1.50/1.72      inference('simplify', [status(thm)], ['16'])).
% 1.50/1.72  thf('18', plain, (((sk_B) = (sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['15', '17'])).
% 1.50/1.72  thf('19', plain, (((sk_A) != (sk_B))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('20', plain, ($false),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 1.50/1.72  
% 1.50/1.72  % SZS output end Refutation
% 1.50/1.72  
% 1.50/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
