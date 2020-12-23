%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2SyRKYCHWv

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:08 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   42 (  82 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  409 ( 999 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2SyRKYCHWv
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 253 iterations in 0.142s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(t98_xboole_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i]:
% 0.38/0.60        ( ( k2_xboole_0 @ A @ B ) =
% 0.38/0.60          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.38/0.60         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d5_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.60         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.38/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['1'])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['1'])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.60         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['1'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.38/0.60          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.38/0.60      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.60          | ~ (r2_hidden @ X4 @ X2)
% 0.38/0.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.38/0.60          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '11'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.38/0.60          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.38/0.60      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['1'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (((k4_xboole_0 @ X1 @ X0)
% 0.38/0.60            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 0.38/0.60          | ~ (r2_hidden @ 
% 0.38/0.60               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.60               X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (((k4_xboole_0 @ X1 @ X0)
% 0.38/0.60            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 0.38/0.60          | ((k4_xboole_0 @ X1 @ X0)
% 0.38/0.60              = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '17'])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k4_xboole_0 @ X1 @ X0)
% 0.38/0.60           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.60  thf(d6_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k5_xboole_0 @ A @ B ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i]:
% 0.38/0.60         ((k5_xboole_0 @ X6 @ X7)
% 0.38/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.38/0.60              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf(t39_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.38/0.60           = (k2_xboole_0 @ X8 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.60           (k4_xboole_0 @ X1 @ X0))
% 0.38/0.60           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['13', '23'])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.38/0.60           = (k2_xboole_0 @ X8 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.60           = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '27'])).
% 0.38/0.60  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
