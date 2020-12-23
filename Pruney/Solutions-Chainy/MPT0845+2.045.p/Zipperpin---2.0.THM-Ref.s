%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSCHZHokLA

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  166 ( 232 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('3',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ X9 @ sk_A )
      | ~ ( r1_xboole_0 @ X9 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( sk_C_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSCHZHokLA
% 0.18/0.37  % Computer   : n007.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 13:05:21 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.37  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 38 iterations in 0.019s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.24/0.51  thf(t3_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf(t7_tarski, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ~( ( r2_hidden @ A @ B ) & 
% 0.24/0.51          ( ![C:$i]:
% 0.24/0.51            ( ~( ( r2_hidden @ C @ B ) & 
% 0.24/0.51                 ( ![D:$i]:
% 0.24/0.51                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7) @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.51  thf(t1_mcart_1, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.51          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.51             ( ![B:$i]:
% 0.24/0.51               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X9 : $i]: (~ (r2_hidden @ X9 @ sk_A) | ~ (r1_xboole_0 @ X9 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X6 @ X7)
% 0.24/0.51          | ~ (r2_hidden @ X8 @ X7)
% 0.24/0.51          | ~ (r2_hidden @ X8 @ (sk_C_1 @ X7)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.24/0.51      inference('condensation', [status(thm)], ['7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.24/0.51          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['6', '8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.24/0.51          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['5', '9'])).
% 0.24/0.51  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.24/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.51  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.24/0.51      inference('demod', [status(thm)], ['4', '11'])).
% 0.24/0.51  thf(t66_xboole_1, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.24/0.51       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X5))),
% 0.24/0.51      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.24/0.51  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.51  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('16', plain, ($false),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
