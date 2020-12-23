%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m0R7CoqRr9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:51 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 112 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 ( 919 expanded)
%              Number of equality atoms :   33 (  78 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t2_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ! [D: $i] :
          ( ~ ( r2_hidden @ D @ A )
        <=> ( ( r2_hidden @ D @ B )
          <=> ( r2_hidden @ D @ C ) ) )
     => ( A
        = ( k5_xboole_0 @ B @ C ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k5_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X8 @ X10 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X8 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X8 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X0
        = ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t92_xboole_1,conjecture,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k5_xboole_0 @ A @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ( k5_xboole_0 @ sk_A @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m0R7CoqRr9
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 232 iterations in 0.179s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.39/0.63  thf(t2_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ![D:$i]:
% 0.39/0.63         ( ( ~( r2_hidden @ D @ A ) ) <=>
% 0.39/0.63           ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.39/0.63       ( ( A ) = ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.63         (((X10) = (k5_xboole_0 @ X8 @ X9))
% 0.39/0.63          | (r2_hidden @ (sk_D_1 @ X9 @ X8 @ X10) @ X8)
% 0.39/0.63          | (r2_hidden @ (sk_D_1 @ X9 @ X8 @ X10) @ X9)
% 0.39/0.63          | (r2_hidden @ (sk_D_1 @ X9 @ X8 @ X10) @ X10))),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_xboole_0])).
% 0.39/0.63  thf(t3_boole, axiom,
% 0.39/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.63  thf('1', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.63  thf(d5_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.63       ( ![D:$i]:
% 0.39/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.63          | ~ (r2_hidden @ X4 @ X2)
% 0.39/0.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X4 @ X2)
% 0.39/0.63          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.63  thf('4', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.63  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ (sk_D_1 @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.39/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.39/0.63          | ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.63  thf('7', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.63  thf(d6_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( k5_xboole_0 @ A @ B ) =
% 0.39/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (![X6 : $i, X7 : $i]:
% 0.39/0.63         ((k5_xboole_0 @ X6 @ X7)
% 0.39/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.39/0.63  thf('9', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.39/0.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.39/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.39/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.39/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.63  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.39/0.63          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.63  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D_1 @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.46/0.63          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.46/0.63      inference('demod', [status(thm)], ['6', '15'])).
% 0.46/0.63  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf(t92_xboole_1, conjecture,
% 0.46/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t92_xboole_1])).
% 0.46/0.63  thf('21', plain, (((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.46/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.46/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.46/0.63          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.46/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 0.46/0.63          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.46/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.46/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.63  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('condensation', [status(thm)], ['4'])).
% 0.46/0.63  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X6 @ X7)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X0 @ X0)
% 0.46/0.63           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['21', '33'])).
% 0.46/0.63  thf('35', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['20', '34'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
