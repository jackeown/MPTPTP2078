%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vNBPz8sE34

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 244 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t21_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vNBPz8sE34
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 34 iterations in 0.046s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(t21_xboole_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.21/0.52          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['1'])).
% 0.21/0.52  thf(d3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ X3)
% 0.21/0.52          | (r2_hidden @ X0 @ X2)
% 0.21/0.52          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 0.21/0.52          | ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 0.21/0.52          | ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.21/0.52          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['1'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain, (((sk_A) != (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.52  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
