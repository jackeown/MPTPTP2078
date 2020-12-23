%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hYpEIN8mpi

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 105 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  382 ( 737 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    | ( r1_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('34',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hYpEIN8mpi
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:39:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 59 iterations in 0.028s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(t77_xboole_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.49          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.49             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.22/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.49          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(t47_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.22/0.49           = (k4_xboole_0 @ X12 @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.22/0.49         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('8', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(t50_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.49       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.22/0.49           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.22/0.49              (k3_xboole_0 @ X19 @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.22/0.49  thf(t49_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.49       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.22/0.49           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.22/0.49           = (k3_xboole_0 @ X19 @ 
% 0.22/0.49              (k4_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X21))))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.22/0.49         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf('14', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X7 : $i, X9 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf(t2_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf('18', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.49          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('20', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf(t48_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.22/0.49           = (k3_xboole_0 @ X14 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.22/0.49           = (k3_xboole_0 @ X14 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.49          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.22/0.49        | (r1_xboole_0 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '31'])).
% 0.22/0.49  thf('33', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.22/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.49  thf('34', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain, ((r1_xboole_0 @ sk_B_1 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('39', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
