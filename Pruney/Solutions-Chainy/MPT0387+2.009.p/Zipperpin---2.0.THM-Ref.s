%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wiWV6Ab3mJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 (  98 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t5_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k1_setfam_1 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t5_setfam_1])).

thf('0',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('2',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_A ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_xboole_0 @ ( k1_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,
    ( ( k1_setfam_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wiWV6Ab3mJ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 19 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t5_setfam_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.46       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.46          ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t5_setfam_1])).
% 0.20/0.46  thf('0', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t4_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((r1_tarski @ (k1_setfam_1 @ X4) @ X5) | ~ (r2_hidden @ X5 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.20/0.46  thf('2', plain, ((r1_tarski @ (k1_setfam_1 @ sk_A) @ k1_xboole_0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.46  thf('3', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.46  thf(t69_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.46       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ X2 @ X3)
% 0.20/0.46          | ~ (r1_tarski @ X2 @ X3)
% 0.20/0.46          | (v1_xboole_0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ((v1_xboole_0 @ (k1_setfam_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.46  thf(l13_xboole_0, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('8', plain, (((k1_setfam_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('10', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
