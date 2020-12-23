%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uks9Rivute

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  177 ( 299 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    sk_A = sk_C ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uks9Rivute
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 19 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(t71_xboole_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.21/0.49         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.49       ( ( A ) = ( C ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.49          ( ( A ) = ( C ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.21/0.49  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d7_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.49  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t51_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.49       ( A ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.49           = (X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.49  thf('7', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.49           = (X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t40_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X4)
% 0.21/0.49           = (k4_xboole_0 @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.49         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X4)
% 0.21/0.49           = (k4_xboole_0 @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_A) = (sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '15'])).
% 0.21/0.49  thf('17', plain, (((sk_A) != (sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
