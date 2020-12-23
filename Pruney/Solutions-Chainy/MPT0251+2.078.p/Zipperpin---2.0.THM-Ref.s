%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rLj7uIy0L7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:12 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  375 ( 568 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X38 @ X40 ) @ X41 )
      | ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r2_hidden @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','27'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rLj7uIy0L7
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:30:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.48  % Solved by: fo/fo7.sh
% 0.24/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.48  % done 116 iterations in 0.034s
% 0.24/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.48  % SZS output start Refutation
% 0.24/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.48  thf(d3_tarski, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.48  thf('0', plain,
% 0.24/0.48      (![X3 : $i, X5 : $i]:
% 0.24/0.48         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.24/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.48  thf(t46_zfmisc_1, conjecture,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r2_hidden @ A @ B ) =>
% 0.24/0.48       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.24/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.48    (~( ![A:$i,B:$i]:
% 0.24/0.48        ( ( r2_hidden @ A @ B ) =>
% 0.24/0.48          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.24/0.48    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.24/0.48  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t38_zfmisc_1, axiom,
% 0.24/0.48    (![A:$i,B:$i,C:$i]:
% 0.24/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.48  thf('3', plain,
% 0.24/0.48      (![X38 : $i, X40 : $i, X41 : $i]:
% 0.24/0.48         ((r1_tarski @ (k2_tarski @ X38 @ X40) @ X41)
% 0.24/0.48          | ~ (r2_hidden @ X40 @ X41)
% 0.24/0.48          | ~ (r2_hidden @ X38 @ X41))),
% 0.24/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.48  thf('4', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (r2_hidden @ X0 @ sk_B)
% 0.24/0.48          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.24/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.48  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.24/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.24/0.48  thf(t69_enumset1, axiom,
% 0.24/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.48  thf('6', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.24/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.48  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.24/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.48  thf(t28_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.48  thf('8', plain,
% 0.24/0.48      (![X18 : $i, X19 : $i]:
% 0.24/0.48         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.24/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.48  thf('9', plain,
% 0.24/0.48      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.24/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.48  thf(t100_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.48  thf('10', plain,
% 0.24/0.48      (![X13 : $i, X14 : $i]:
% 0.24/0.48         ((k4_xboole_0 @ X13 @ X14)
% 0.24/0.48           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.48  thf('11', plain,
% 0.24/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.24/0.48         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.24/0.48  thf(t1_xboole_0, axiom,
% 0.24/0.48    (![A:$i,B:$i,C:$i]:
% 0.24/0.48     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.24/0.48       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.24/0.48  thf('12', plain,
% 0.24/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.48         ((r2_hidden @ X6 @ X7)
% 0.24/0.48          | (r2_hidden @ X6 @ X8)
% 0.24/0.48          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.24/0.48  thf('13', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.24/0.48          | (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.48          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.48  thf('14', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.48          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.24/0.48  thf('15', plain,
% 0.24/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.24/0.48         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.24/0.48  thf('16', plain,
% 0.24/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.24/0.48          | ~ (r2_hidden @ X6 @ X8)
% 0.24/0.48          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.24/0.48  thf('17', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.24/0.48          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.48          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.48  thf('18', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.48          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.24/0.48  thf('19', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.24/0.48      inference('clc', [status(thm)], ['14', '18'])).
% 0.24/0.48  thf('20', plain,
% 0.24/0.48      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 0.24/0.48      inference('sup-', [status(thm)], ['0', '19'])).
% 0.24/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.24/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.24/0.48  thf('21', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.48  thf(t1_boole, axiom,
% 0.24/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.48  thf('22', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.24/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.48  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.24/0.48  thf(t7_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.48  thf('24', plain,
% 0.24/0.48      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.24/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.48  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.48  thf(d10_xboole_0, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.48  thf('26', plain,
% 0.24/0.48      (![X10 : $i, X12 : $i]:
% 0.24/0.48         (((X10) = (X12))
% 0.24/0.48          | ~ (r1_tarski @ X12 @ X10)
% 0.24/0.48          | ~ (r1_tarski @ X10 @ X12))),
% 0.24/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.48  thf('27', plain,
% 0.24/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.48  thf('28', plain,
% 0.24/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['20', '27'])).
% 0.24/0.48  thf(t39_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.48  thf('29', plain,
% 0.24/0.48      (![X20 : $i, X21 : $i]:
% 0.24/0.48         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.24/0.48           = (k2_xboole_0 @ X20 @ X21))),
% 0.24/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.24/0.48  thf('30', plain,
% 0.24/0.48      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.24/0.48         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.24/0.48  thf('31', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.24/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.48  thf('32', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.24/0.48  thf('33', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('34', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.48  thf('35', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.24/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.24/0.48  thf('36', plain, ($false),
% 0.24/0.48      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.24/0.48  
% 0.24/0.48  % SZS output end Refutation
% 0.24/0.48  
% 0.24/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
