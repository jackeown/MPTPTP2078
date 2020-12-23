%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KFr5sYZ5c

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:08 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t46_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t46_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KFr5sYZ5c
% 0.16/0.38  % Computer   : n018.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 17:42:57 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.50  % Solved by: fo/fo7.sh
% 0.25/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.50  % done 4 iterations in 0.007s
% 0.25/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.50  % SZS output start Refutation
% 0.25/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.50  thf(t46_xboole_1, conjecture,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.25/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.50    (~( ![A:$i,B:$i]:
% 0.25/0.50        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ) )),
% 0.25/0.50    inference('cnf.neg', [status(esa)], [t46_xboole_1])).
% 0.25/0.50  thf('0', plain,
% 0.25/0.50      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf(t7_xboole_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.25/0.50  thf('1', plain,
% 0.25/0.50      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.25/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.25/0.50  thf(l32_xboole_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.50  thf('2', plain,
% 0.25/0.50      (![X0 : $i, X2 : $i]:
% 0.25/0.50         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.25/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.25/0.50  thf('3', plain,
% 0.25/0.50      (![X0 : $i, X1 : $i]:
% 0.25/0.50         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.25/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.50  thf('4', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.25/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.25/0.50  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.25/0.50  
% 0.25/0.50  % SZS output end Refutation
% 0.25/0.50  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
