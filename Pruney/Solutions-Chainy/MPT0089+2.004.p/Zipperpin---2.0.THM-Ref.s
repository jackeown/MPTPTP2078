%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xa9No3iLGw

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:39 EST 2020

% Result     : Theorem 13.73s
% Output     : Refutation 13.73s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  281 ( 385 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t82_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t82_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xa9No3iLGw
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:07:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 13.73/13.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.73/13.97  % Solved by: fo/fo7.sh
% 13.73/13.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.73/13.97  % done 10076 iterations in 13.493s
% 13.73/13.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.73/13.97  % SZS output start Refutation
% 13.73/13.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.73/13.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 13.73/13.97  thf(sk_B_type, type, sk_B: $i).
% 13.73/13.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.73/13.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.73/13.97  thf(sk_A_type, type, sk_A: $i).
% 13.73/13.97  thf(t82_xboole_1, conjecture,
% 13.73/13.97    (![A:$i,B:$i]:
% 13.73/13.97     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 13.73/13.97  thf(zf_stmt_0, negated_conjecture,
% 13.73/13.97    (~( ![A:$i,B:$i]:
% 13.73/13.97        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )),
% 13.73/13.97    inference('cnf.neg', [status(esa)], [t82_xboole_1])).
% 13.73/13.97  thf('0', plain,
% 13.73/13.97      (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 13.73/13.97          (k4_xboole_0 @ sk_B @ sk_A))),
% 13.73/13.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.97  thf(d5_xboole_0, axiom,
% 13.73/13.97    (![A:$i,B:$i,C:$i]:
% 13.73/13.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 13.73/13.97       ( ![D:$i]:
% 13.73/13.97         ( ( r2_hidden @ D @ C ) <=>
% 13.73/13.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 13.73/13.97  thf('1', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 13.73/13.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 13.73/13.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 13.73/13.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 13.73/13.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 13.73/13.97  thf('2', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 13.73/13.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.73/13.97      inference('eq_fact', [status(thm)], ['1'])).
% 13.73/13.97  thf('3', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.73/13.97         (~ (r2_hidden @ X4 @ X3)
% 13.73/13.97          | (r2_hidden @ X4 @ X1)
% 13.73/13.97          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 13.73/13.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 13.73/13.97  thf('4', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 13.73/13.97         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 13.73/13.97      inference('simplify', [status(thm)], ['3'])).
% 13.73/13.97  thf('5', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.97         (((k4_xboole_0 @ X1 @ X0)
% 13.73/13.97            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 13.73/13.97          | (r2_hidden @ 
% 13.73/13.97             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 13.73/13.97             X1))),
% 13.73/13.97      inference('sup-', [status(thm)], ['2', '4'])).
% 13.73/13.97  thf('6', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 13.73/13.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.73/13.97      inference('eq_fact', [status(thm)], ['1'])).
% 13.73/13.97  thf('7', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 13.73/13.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 13.73/13.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 13.73/13.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 13.73/13.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 13.73/13.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 13.73/13.97  thf('8', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 13.73/13.97          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 13.73/13.97          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 13.73/13.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.73/13.97      inference('sup-', [status(thm)], ['6', '7'])).
% 13.73/13.97  thf('9', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 13.73/13.97          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 13.73/13.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.73/13.97      inference('simplify', [status(thm)], ['8'])).
% 13.73/13.97  thf('10', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 13.73/13.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.73/13.97      inference('eq_fact', [status(thm)], ['1'])).
% 13.73/13.97  thf('11', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i]:
% 13.73/13.97         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 13.73/13.97          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 13.73/13.97      inference('clc', [status(thm)], ['9', '10'])).
% 13.73/13.97  thf('12', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.73/13.97         (~ (r2_hidden @ X4 @ X3)
% 13.73/13.97          | ~ (r2_hidden @ X4 @ X2)
% 13.73/13.97          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 13.73/13.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 13.73/13.97  thf('13', plain,
% 13.73/13.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 13.73/13.97         (~ (r2_hidden @ X4 @ X2)
% 13.73/13.97          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 13.73/13.97      inference('simplify', [status(thm)], ['12'])).
% 13.73/13.97  thf('14', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.97         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 13.73/13.97          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 13.73/13.97      inference('sup-', [status(thm)], ['11', '13'])).
% 13.73/13.97  thf('15', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.97         (((k4_xboole_0 @ X0 @ X1)
% 13.73/13.97            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))
% 13.73/13.97          | ((k4_xboole_0 @ X0 @ X1)
% 13.73/13.97              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 13.73/13.97                 (k4_xboole_0 @ X2 @ X0))))),
% 13.73/13.97      inference('sup-', [status(thm)], ['5', '14'])).
% 13.73/13.97  thf('16', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.97         ((k4_xboole_0 @ X0 @ X1)
% 13.73/13.97           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 13.73/13.97      inference('simplify', [status(thm)], ['15'])).
% 13.73/13.97  thf(t79_xboole_1, axiom,
% 13.73/13.97    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 13.73/13.97  thf('17', plain,
% 13.73/13.97      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 13.73/13.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 13.73/13.97  thf('18', plain,
% 13.73/13.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.97         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1))),
% 13.73/13.97      inference('sup+', [status(thm)], ['16', '17'])).
% 13.73/13.97  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 13.73/13.97  
% 13.73/13.97  % SZS output end Refutation
% 13.73/13.97  
% 13.73/13.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
