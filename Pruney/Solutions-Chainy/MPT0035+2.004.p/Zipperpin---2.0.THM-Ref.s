%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xcCpCITeJu

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  183 ( 255 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ X3 @ ( sk_D @ X3 @ X2 @ X1 ) )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( sk_D @ X3 @ X2 @ X1 ) )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('8',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xcCpCITeJu
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 19 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.48  thf('0', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('2', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t28_xboole_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t28_xboole_1])).
% 0.21/0.48  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t14_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.21/0.48         ( ![D:$i]:
% 0.21/0.48           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.48             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.21/0.48       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X2)
% 0.21/0.48          | (r1_tarski @ X3 @ (sk_D @ X3 @ X2 @ X1))
% 0.21/0.48          | ((X2) = (k2_xboole_0 @ X1 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_B) = (k2_xboole_0 @ sk_A @ X0))
% 0.21/0.48          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.21/0.48          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X2 @ (sk_D @ X3 @ X2 @ X1))
% 0.21/0.48          | ((X2) = (k2_xboole_0 @ X1 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.21/0.48        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (r1_tarski @ sk_B @ sk_B)
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.21/0.48        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.48  thf('12', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.48  thf(t21_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.48  thf('14', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
