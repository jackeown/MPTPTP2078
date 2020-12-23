%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWU04JSnOv

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   32 (  48 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 ( 617 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t5_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWU04JSnOv
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:33:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 80 iterations in 0.097s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(t5_xboole_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56          ( k2_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t5_xboole_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (((k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.37/0.56         != (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ 
% 0.37/0.56             (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t4_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.37/0.56           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.37/0.56           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.37/0.56         != (k2_xboole_0 @ sk_A @ 
% 0.37/0.56             (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.37/0.56  thf(d3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.56       ( ![D:$i]:
% 0.37/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.37/0.56         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.37/0.56         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.37/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ X0 @ X2)
% 0.37/0.56          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.37/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.37/0.56         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 0.37/0.56          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 0.37/0.56          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k2_xboole_0 @ X1 @ X0)
% 0.37/0.56            = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.37/0.56          | ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.56              = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.37/0.56         != (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['3', '19'])).
% 0.37/0.56  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
