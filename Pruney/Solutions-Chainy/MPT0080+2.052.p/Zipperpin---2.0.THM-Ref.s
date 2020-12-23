%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.39eLMFUeZc

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  252 ( 296 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X14 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.39eLMFUeZc
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 209 iterations in 0.109s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(t73_xboole_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.57       ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.57            ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.57          ( r1_tarski @ A @ B ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.21/0.57  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.57  thf('3', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t43_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.21/0.57       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.21/0.57          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.21/0.57  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_2)),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(t63_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.57       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X22 @ X23)
% 0.21/0.57          | ~ (r1_xboole_0 @ X23 @ X24)
% 0.21/0.57          | (r1_xboole_0 @ X22 @ X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.21/0.57          | ~ (r1_xboole_0 @ sk_C_2 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf(t36_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.57  thf(t28_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.21/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf(t4_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.21/0.57          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.57          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.57          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.57  thf(t38_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.57       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.57  thf('19', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf(t37_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         ((r1_tarski @ X14 @ X15)
% 0.21/0.57          | ((k4_xboole_0 @ X14 @ X15) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.57  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
