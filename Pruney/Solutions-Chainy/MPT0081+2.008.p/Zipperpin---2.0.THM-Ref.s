%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.86JlHldPfQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :  218 ( 279 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

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

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.86JlHldPfQ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 100 iterations in 0.025s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.43  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(t74_xboole_1, conjecture,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.43          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.43        ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.43             ( r1_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t74_xboole_1])).
% 0.21/0.44  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_2))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d7_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.44       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.44  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.44  thf(t4_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.44            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X8 : $i, X9 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X8 @ X9)
% 0.21/0.44          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.44  thf(t16_xboole_1, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.44       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.44         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.21/0.44           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.21/0.44          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.44          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.44          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.44          | (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.44  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.44  thf('10', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i, X2 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.44  thf('13', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.44      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.44  thf(t3_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.44            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.44  thf('15', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.21/0.44          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.44  thf('17', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.44  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.21/0.44      inference('demod', [status(thm)], ['9', '19'])).
% 0.21/0.44  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
