%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GOOHb2qqrJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 208 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X7 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r2_hidden @ X11 @ ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X10 @ X8 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['2','13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GOOHb2qqrJ
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 22 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(t4_setfam_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.20/0.46  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d1_xboole_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.46  thf('2', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d3_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]:
% 0.20/0.46         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf(d1_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.20/0.46         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.46       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.46         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.46               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.46          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.46          | (r2_hidden @ X11 @ X10)
% 0.20/0.46          | ~ (r2_hidden @ X11 @ X7)
% 0.20/0.46          | ((X8) = (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         (((X8) = (k1_xboole_0))
% 0.20/0.46          | ~ (r2_hidden @ X11 @ (k1_setfam_1 @ X8))
% 0.20/0.46          | (r2_hidden @ X11 @ X10)
% 0.20/0.46          | ~ (r2_hidden @ X10 @ X8))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.20/0.46          | ~ (r2_hidden @ X2 @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.20/0.46          | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((sk_B_1) = (k1_xboole_0))
% 0.20/0.46          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B_1)) @ sk_A)
% 0.20/0.46          | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]:
% 0.20/0.46         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)
% 0.20/0.46        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.46        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.46        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 0.20/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  thf('12', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.46  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('15', plain, ($false),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '13', '14'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
