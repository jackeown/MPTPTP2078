%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvjR0vO7zC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:27 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 215 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X12 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_2 )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvjR0vO7zC
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:49:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.46  % Solved by: fo/fo7.sh
% 0.25/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.46  % done 15 iterations in 0.009s
% 0.25/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.46  % SZS output start Refutation
% 0.25/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.25/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.46  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.25/0.46  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.25/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.46  thf(t78_xboole_1, conjecture,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( r1_xboole_0 @ A @ B ) =>
% 0.25/0.46       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.25/0.46         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.25/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.46        ( ( r1_xboole_0 @ A @ B ) =>
% 0.25/0.46          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.25/0.46            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.25/0.46    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.25/0.46  thf('0', plain,
% 0.25/0.46      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.25/0.46         != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(t61_xboole_1, axiom,
% 0.25/0.46    (![A:$i]:
% 0.25/0.46     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.25/0.46  thf('2', plain,
% 0.25/0.46      (![X12 : $i]:
% 0.25/0.46         ((r2_xboole_0 @ k1_xboole_0 @ X12) | ((X12) = (k1_xboole_0)))),
% 0.25/0.46      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.25/0.46  thf(t6_xboole_0, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.25/0.46          ( ![C:$i]:
% 0.25/0.46            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.25/0.46  thf('3', plain,
% 0.25/0.46      (![X4 : $i, X5 : $i]:
% 0.25/0.46         (~ (r2_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.25/0.46      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.25/0.46  thf('4', plain,
% 0.25/0.46      (![X0 : $i]:
% 0.25/0.46         (((X0) = (k1_xboole_0))
% 0.25/0.46          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.25/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.46  thf(t4_xboole_0, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.25/0.46  thf('5', plain,
% 0.25/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.25/0.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.25/0.46          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.25/0.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.46  thf('6', plain,
% 0.25/0.46      (![X0 : $i, X1 : $i]:
% 0.25/0.46         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.25/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.46  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.25/0.46      inference('sup-', [status(thm)], ['1', '6'])).
% 0.25/0.46  thf(t23_xboole_1, axiom,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.25/0.46       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.25/0.46  thf('8', plain,
% 0.25/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.46         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.25/0.46           = (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 0.25/0.46      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.25/0.46  thf('9', plain,
% 0.25/0.46      (![X0 : $i]:
% 0.25/0.46         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.25/0.46           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.25/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.25/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.25/0.46  thf('10', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.25/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.25/0.46  thf(t12_xboole_1, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.25/0.46  thf('11', plain,
% 0.25/0.46      (![X6 : $i, X7 : $i]:
% 0.25/0.46         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.25/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.25/0.46  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.25/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.46  thf('13', plain,
% 0.25/0.46      (![X0 : $i]:
% 0.25/0.46         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.25/0.46           = (k3_xboole_0 @ sk_A @ X0))),
% 0.25/0.46      inference('demod', [status(thm)], ['9', '12'])).
% 0.25/0.46  thf('14', plain,
% 0.25/0.46      (((k3_xboole_0 @ sk_A @ sk_C_2) != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.25/0.46      inference('demod', [status(thm)], ['0', '13'])).
% 0.25/0.46  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.25/0.46  
% 0.25/0.46  % SZS output end Refutation
% 0.25/0.46  
% 0.25/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
