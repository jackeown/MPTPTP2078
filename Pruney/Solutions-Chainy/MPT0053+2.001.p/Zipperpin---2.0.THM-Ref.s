%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yzqA76HOUE

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   40 (  91 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 ( 650 expanded)
%              Number of equality atoms :   28 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['2','20','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yzqA76HOUE
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 79 iterations in 0.088s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.19/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(t46_xboole_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t46_xboole_1])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t41_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.54       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.54           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf(d5_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.54       ( ![D:$i]:
% 0.37/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.37/0.54         (((X13) = (k4_xboole_0 @ X9 @ X10))
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X9)
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf(t1_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('5', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.54  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.54  thf(t39_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.37/0.54           = (k2_xboole_0 @ X15 @ X16))),
% 0.37/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X12 @ X11)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ X10)
% 0.37/0.54          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X12 @ X10)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.54  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.54          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.37/0.54         (((X13) = (k4_xboole_0 @ X9 @ X10))
% 0.37/0.54          | ~ (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X10)
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.37/0.54          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.37/0.54          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.54  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.54  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.54          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '14'])).
% 0.37/0.54  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['2', '20', '23'])).
% 0.37/0.54  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
