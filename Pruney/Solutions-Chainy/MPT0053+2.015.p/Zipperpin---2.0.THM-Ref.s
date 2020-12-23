%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oE3Svbqu6P

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 ( 423 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t46_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t46_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
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
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oE3Svbqu6P
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 60 iterations in 0.064s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.52  thf(t46_xboole_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t46_xboole_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d5_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('2', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.52          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.52          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.52          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.21/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.21/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.52  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['5'])).
% 0.21/0.52  thf('12', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t41_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.52       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.21/0.52           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.52           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.52  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['5'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.52  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.52  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
