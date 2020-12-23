%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQ3FpGhN7T

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  369 ( 450 expanded)
%              Number of equality atoms :   28 (  29 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQ3FpGhN7T
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.77  % Solved by: fo/fo7.sh
% 0.55/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.77  % done 653 iterations in 0.309s
% 0.55/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.77  % SZS output start Refutation
% 0.55/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.77  thf(t48_xboole_1, conjecture,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.77    (~( ![A:$i,B:$i]:
% 0.55/0.77        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.55/0.77          ( k3_xboole_0 @ A @ B ) ) )),
% 0.55/0.77    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.55/0.77  thf('0', plain,
% 0.55/0.77      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.55/0.77         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(t47_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf('1', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.55/0.77           = (k4_xboole_0 @ X22 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.55/0.77  thf(t39_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf('2', plain,
% 0.55/0.77      (![X17 : $i, X18 : $i]:
% 0.55/0.77         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.55/0.77           = (k2_xboole_0 @ X17 @ X18))),
% 0.55/0.77      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.55/0.77  thf(t40_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf('3', plain,
% 0.55/0.77      (![X20 : $i, X21 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.55/0.77           = (k4_xboole_0 @ X20 @ X21))),
% 0.55/0.77      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.77  thf('4', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.55/0.77           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.77  thf(t3_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.55/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.77  thf('5', plain,
% 0.55/0.77      (![X11 : $i, X12 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.77  thf('6', plain,
% 0.55/0.77      (![X11 : $i, X12 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.77  thf(d5_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i]:
% 0.55/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.55/0.77       ( ![D:$i]:
% 0.55/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.55/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.55/0.77  thf('7', plain,
% 0.55/0.77      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.55/0.77         (~ (r2_hidden @ X6 @ X5)
% 0.55/0.77          | ~ (r2_hidden @ X6 @ X4)
% 0.55/0.77          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.55/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.55/0.77  thf('8', plain,
% 0.55/0.77      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.55/0.77         (~ (r2_hidden @ X6 @ X4)
% 0.55/0.77          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.55/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.55/0.77  thf('9', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.55/0.77          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['6', '8'])).
% 0.55/0.77  thf('10', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.55/0.77          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['5', '9'])).
% 0.55/0.77  thf('11', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.55/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.55/0.77  thf('12', plain,
% 0.55/0.77      (![X11 : $i, X12 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.77  thf('13', plain,
% 0.55/0.77      (![X11 : $i, X12 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.77  thf('14', plain,
% 0.55/0.77      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.55/0.77         (~ (r2_hidden @ X13 @ X11)
% 0.55/0.77          | ~ (r2_hidden @ X13 @ X14)
% 0.55/0.77          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.77  thf('15', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X1 @ X0)
% 0.55/0.77          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.55/0.77          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.55/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.77  thf('16', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((r1_xboole_0 @ X0 @ X1)
% 0.55/0.77          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.55/0.77          | (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.77      inference('sup-', [status(thm)], ['12', '15'])).
% 0.55/0.77  thf('17', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.55/0.77  thf('18', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['11', '17'])).
% 0.55/0.77  thf(d7_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.55/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.77  thf('19', plain,
% 0.55/0.77      (![X8 : $i, X9 : $i]:
% 0.55/0.77         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.55/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.55/0.77  thf('20', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.77  thf('21', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.55/0.77           = (k4_xboole_0 @ X22 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.55/0.77  thf('22', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.55/0.77           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['20', '21'])).
% 0.55/0.77  thf(t3_boole, axiom,
% 0.55/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.77  thf('23', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.55/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.55/0.77  thf('24', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.55/0.77  thf('25', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.55/0.77           = (X1))),
% 0.55/0.77      inference('demod', [status(thm)], ['4', '24'])).
% 0.55/0.77  thf('26', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.55/0.77           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.77      inference('sup+', [status(thm)], ['1', '25'])).
% 0.55/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.77  thf('27', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.77  thf(t22_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.55/0.77  thf('28', plain,
% 0.55/0.77      (![X15 : $i, X16 : $i]:
% 0.55/0.77         ((k2_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)) = (X15))),
% 0.55/0.77      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.55/0.77  thf('29', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.55/0.77  thf('30', plain,
% 0.55/0.77      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.77      inference('demod', [status(thm)], ['0', '29'])).
% 0.55/0.77  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.55/0.77  
% 0.55/0.77  % SZS output end Refutation
% 0.55/0.77  
% 0.55/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
