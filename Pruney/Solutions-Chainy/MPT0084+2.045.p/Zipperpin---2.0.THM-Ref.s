%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g9TApOyVrx

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  311 ( 383 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t26_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['16','25'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g9TApOyVrx
% 0.15/0.36  % Computer   : n005.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:59:48 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 1.40/1.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.40/1.58  % Solved by: fo/fo7.sh
% 1.40/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.40/1.58  % done 2530 iterations in 1.117s
% 1.40/1.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.40/1.58  % SZS output start Refutation
% 1.40/1.58  thf(sk_B_type, type, sk_B: $i).
% 1.40/1.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.40/1.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.40/1.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.40/1.58  thf(sk_C_type, type, sk_C: $i).
% 1.40/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.40/1.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.40/1.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.40/1.58  thf(t77_xboole_1, conjecture,
% 1.40/1.58    (![A:$i,B:$i,C:$i]:
% 1.40/1.58     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.40/1.58          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.40/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.40/1.58    (~( ![A:$i,B:$i,C:$i]:
% 1.40/1.58        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.40/1.58             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 1.40/1.58    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 1.40/1.58  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('1', plain, ((r1_tarski @ sk_A @ sk_C)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.40/1.58  thf('2', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 1.40/1.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.40/1.58  thf(d7_xboole_0, axiom,
% 1.40/1.58    (![A:$i,B:$i]:
% 1.40/1.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.40/1.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.40/1.58  thf('3', plain,
% 1.40/1.58      (![X0 : $i, X1 : $i]:
% 1.40/1.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.40/1.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.40/1.58  thf('4', plain,
% 1.40/1.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['2', '3'])).
% 1.40/1.58  thf(t31_xboole_1, axiom,
% 1.40/1.58    (![A:$i,B:$i,C:$i]:
% 1.40/1.58     ( r1_tarski @
% 1.40/1.58       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.40/1.59       ( k2_xboole_0 @ B @ C ) ))).
% 1.40/1.59  thf('5', plain,
% 1.40/1.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.40/1.59         (r1_tarski @ 
% 1.40/1.59          (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X20)) @ 
% 1.40/1.59          (k2_xboole_0 @ X19 @ X20))),
% 1.40/1.59      inference('cnf', [status(esa)], [t31_xboole_1])).
% 1.40/1.59  thf('6', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.40/1.59          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['4', '5'])).
% 1.40/1.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.40/1.59  thf('7', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 1.40/1.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.40/1.59  thf(t12_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.40/1.59  thf('8', plain,
% 1.40/1.59      (![X5 : $i, X6 : $i]:
% 1.40/1.59         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.40/1.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.40/1.59  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.40/1.59      inference('sup-', [status(thm)], ['7', '8'])).
% 1.40/1.59  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.40/1.59      inference('sup-', [status(thm)], ['7', '8'])).
% 1.40/1.59  thf('11', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.40/1.59      inference('demod', [status(thm)], ['6', '9', '10'])).
% 1.40/1.59  thf(t1_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.40/1.59       ( r1_tarski @ A @ C ) ))).
% 1.40/1.59  thf('12', plain,
% 1.40/1.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.40/1.59         (~ (r1_tarski @ X9 @ X10)
% 1.40/1.59          | ~ (r1_tarski @ X10 @ X11)
% 1.40/1.59          | (r1_tarski @ X9 @ X11))),
% 1.40/1.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.40/1.59  thf('13', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.40/1.59      inference('sup-', [status(thm)], ['11', '12'])).
% 1.40/1.59  thf('14', plain,
% 1.40/1.59      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['1', '13'])).
% 1.40/1.59  thf(t28_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.40/1.59  thf('15', plain,
% 1.40/1.59      (![X15 : $i, X16 : $i]:
% 1.40/1.59         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.40/1.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.40/1.59  thf('16', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)
% 1.40/1.59           = (k3_xboole_0 @ X0 @ sk_A))),
% 1.40/1.59      inference('sup-', [status(thm)], ['14', '15'])).
% 1.40/1.59  thf('17', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(symmetry_r1_xboole_0, axiom,
% 1.40/1.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.40/1.59  thf('18', plain,
% 1.40/1.59      (![X3 : $i, X4 : $i]:
% 1.40/1.59         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.40/1.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.40/1.59  thf('19', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.40/1.59      inference('sup-', [status(thm)], ['17', '18'])).
% 1.40/1.59  thf(t17_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.40/1.59  thf('20', plain,
% 1.40/1.59      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.40/1.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.40/1.59  thf(t26_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( r1_tarski @ A @ B ) =>
% 1.40/1.59       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.40/1.59  thf('21', plain,
% 1.40/1.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.40/1.59         (~ (r1_tarski @ X12 @ X13)
% 1.40/1.59          | (r1_tarski @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X14)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t26_xboole_1])).
% 1.40/1.59  thf('22', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 1.40/1.59          (k3_xboole_0 @ X0 @ X2))),
% 1.40/1.59      inference('sup-', [status(thm)], ['20', '21'])).
% 1.40/1.59  thf(t63_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.40/1.59       ( r1_xboole_0 @ A @ C ) ))).
% 1.40/1.59  thf('23', plain,
% 1.40/1.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.40/1.59         (~ (r1_tarski @ X21 @ X22)
% 1.40/1.59          | ~ (r1_xboole_0 @ X22 @ X23)
% 1.40/1.59          | (r1_xboole_0 @ X21 @ X23))),
% 1.40/1.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.40/1.59  thf('24', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.40/1.59         ((r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ X3)
% 1.40/1.59          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X3))),
% 1.40/1.59      inference('sup-', [status(thm)], ['22', '23'])).
% 1.40/1.59  thf('25', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C) @ sk_A)),
% 1.40/1.59      inference('sup-', [status(thm)], ['19', '24'])).
% 1.40/1.59  thf('26', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 1.40/1.59      inference('sup+', [status(thm)], ['16', '25'])).
% 1.40/1.59  thf(t75_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.40/1.59          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 1.40/1.59  thf('27', plain,
% 1.40/1.59      (![X25 : $i, X26 : $i]:
% 1.40/1.59         ((r1_xboole_0 @ X25 @ X26)
% 1.40/1.59          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ X26))),
% 1.40/1.59      inference('cnf', [status(esa)], [t75_xboole_1])).
% 1.40/1.59  thf('28', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.40/1.59      inference('sup-', [status(thm)], ['26', '27'])).
% 1.40/1.59  thf('29', plain,
% 1.40/1.59      (![X3 : $i, X4 : $i]:
% 1.40/1.59         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.40/1.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.40/1.59  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 1.40/1.59      inference('sup-', [status(thm)], ['28', '29'])).
% 1.40/1.59  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 1.40/1.59  
% 1.40/1.59  % SZS output end Refutation
% 1.40/1.59  
% 1.40/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
