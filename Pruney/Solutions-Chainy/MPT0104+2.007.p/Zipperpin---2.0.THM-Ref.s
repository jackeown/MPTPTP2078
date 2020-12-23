%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wylGl5AAqc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:04 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 174 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t97_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
          & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t97_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wylGl5AAqc
% 0.14/0.36  % Computer   : n019.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:50:37 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 8 iterations in 0.011s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(t97_xboole_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.23/0.49         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.23/0.49       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.23/0.49            ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.23/0.49          ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t97_xboole_1])).
% 0.23/0.49  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('2', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t8_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.23/0.49       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X2 @ X3)
% 0.23/0.49          | ~ (r1_tarski @ X4 @ X3)
% 0.23/0.49          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((r1_tarski @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ sk_C)
% 0.23/0.49          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      ((r1_tarski @ 
% 0.23/0.49        (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.23/0.49         (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 0.23/0.49        sk_C)),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.23/0.49  thf(d6_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k5_xboole_0 @ A @ B ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((k5_xboole_0 @ X0 @ X1)
% 0.23/0.49           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.23/0.49  thf('7', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.23/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.49  thf('8', plain, ($false), inference('demod', [status(thm)], ['0', '7'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
