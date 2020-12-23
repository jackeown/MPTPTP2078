%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwAZ37Nei1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  214 ( 251 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X13
       != ( k1_setfam_1 @ X14 ) )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X17 @ X13 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ ( k1_setfam_1 @ X14 ) )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X16 @ X14 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['2','13','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwAZ37Nei1
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 99 iterations in 0.079s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(t4_setfam_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.21/0.53  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('2', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(d1_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.53               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (((X13) != (k1_setfam_1 @ X14))
% 0.21/0.53          | ~ (r2_hidden @ X16 @ X14)
% 0.21/0.53          | (r2_hidden @ X17 @ X16)
% 0.21/0.53          | ~ (r2_hidden @ X17 @ X13)
% 0.21/0.53          | ((X14) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (((X14) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X17 @ (k1_setfam_1 @ X14))
% 0.21/0.53          | (r2_hidden @ X17 @ X16)
% 0.21/0.53          | ~ (r2_hidden @ X16 @ X14))),
% 0.21/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.21/0.53          | ~ (r2_hidden @ X2 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B_1) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B_1)) @ sk_A)
% 0.21/0.53          | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (((r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)
% 0.21/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.53  thf('12', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('15', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.21/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('16', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(t69_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.53       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X11 @ X12)
% 0.21/0.53          | ~ (r1_tarski @ X11 @ X12)
% 0.21/0.53          | (v1_xboole_0 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.53  thf('20', plain, ($false),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '13', '19'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
