%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08n0Dzyev1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  160 ( 248 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t28_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( k3_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t28_xboole_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( sk_D @ X3 @ X2 @ X1 ) @ X2 )
      | ( X1
        = ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( sk_D @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_tarski @ ( sk_D @ X3 @ X2 @ X1 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('10',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08n0Dzyev1
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:00:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 20 iterations in 0.014s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.47  thf(t28_xboole_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t28_xboole_1])).
% 0.21/0.47  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t1_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.47  thf(t7_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.47  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t20_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.47         ( ![D:$i]:
% 0.21/0.47           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.21/0.47             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.21/0.47       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X3)
% 0.21/0.47          | (r1_tarski @ (sk_D @ X3 @ X2 @ X1) @ X2)
% 0.21/0.47          | ((X1) = (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.21/0.47          | (r1_tarski @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.21/0.47          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((r1_tarski @ (sk_D @ sk_B @ sk_A @ sk_A) @ sk_A)
% 0.21/0.47        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.47  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain, ((r1_tarski @ (sk_D @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X3)
% 0.21/0.47          | ~ (r1_tarski @ (sk_D @ X3 @ X2 @ X1) @ X1)
% 0.21/0.47          | ((X1) = (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.47        | ~ (r1_tarski @ sk_A @ sk_B)
% 0.21/0.47        | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.47  thf('14', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
