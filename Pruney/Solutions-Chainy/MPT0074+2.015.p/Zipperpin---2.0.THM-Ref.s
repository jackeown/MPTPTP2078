%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wEj4rK61ZU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 ( 312 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wEj4rK61ZU
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 76 iterations in 0.029s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(t2_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.49       ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((X3) = (X2))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X2 @ X3) @ X2)
% 0.21/0.49          | (r2_hidden @ (sk_C @ X2 @ X3) @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.49  thf(t67_xboole_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.49         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.49            ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.21/0.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X8 : $i, X10 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t48_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.49           = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t3_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('6', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.49  thf('7', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t4_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.21/0.49          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ sk_A) | ~ (r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t63_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X15 @ X16)
% 0.21/0.49          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.21/0.49          | (r1_xboole_0 @ X15 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.49  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]: ((r2_hidden @ (sk_C @ sk_A @ X0) @ X0) | ((X0) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '15'])).
% 0.21/0.49  thf(t2_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.21/0.49          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.49  thf('20', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.49  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.49  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
