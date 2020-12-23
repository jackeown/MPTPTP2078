%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b1YQTPC42

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  255 ( 421 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('1',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('25',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b1YQTPC42
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 12:37:06 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.35/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.60  % Solved by: fo/fo7.sh
% 0.35/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.60  % done 212 iterations in 0.109s
% 0.35/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.60  % SZS output start Refutation
% 0.35/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.60  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.35/0.60  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.35/0.60  thf('0', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.35/0.60      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.35/0.60  thf(t12_ordinal1, conjecture,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.35/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.60    (~( ![A:$i,B:$i]:
% 0.35/0.60        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.35/0.60    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.35/0.60  thf('1', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(d1_ordinal1, axiom,
% 0.35/0.60    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.35/0.60  thf('2', plain,
% 0.35/0.60      (![X15 : $i]:
% 0.35/0.60         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 0.35/0.60      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.35/0.60  thf(d3_xboole_0, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.60       ( ![D:$i]:
% 0.35/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.60           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.60  thf('3', plain,
% 0.35/0.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.60          | (r2_hidden @ X6 @ X5)
% 0.35/0.60          | (r2_hidden @ X6 @ X3)
% 0.35/0.60          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.60  thf('4', plain,
% 0.35/0.60      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.35/0.60         ((r2_hidden @ X6 @ X3)
% 0.35/0.60          | (r2_hidden @ X6 @ X5)
% 0.35/0.60          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.60  thf('5', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.35/0.60          | (r2_hidden @ X1 @ X0)
% 0.35/0.60          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['2', '4'])).
% 0.35/0.60  thf('6', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))
% 0.35/0.60          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.35/0.60          | (r2_hidden @ X0 @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['1', '5'])).
% 0.35/0.60  thf('7', plain,
% 0.35/0.60      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['0', '6'])).
% 0.35/0.60  thf('8', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('9', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.35/0.60      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.35/0.60  thf('10', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.35/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.60  thf('11', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.35/0.60          | (r2_hidden @ X1 @ X0)
% 0.35/0.60          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['2', '4'])).
% 0.35/0.60  thf('12', plain,
% 0.35/0.60      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.60  thf(t69_enumset1, axiom,
% 0.35/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.60  thf('13', plain,
% 0.35/0.60      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.35/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.60  thf(d2_tarski, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.35/0.60       ( ![D:$i]:
% 0.35/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.35/0.60  thf('14', plain,
% 0.35/0.60      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X12 @ X10)
% 0.35/0.60          | ((X12) = (X11))
% 0.35/0.60          | ((X12) = (X8))
% 0.35/0.60          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.35/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.35/0.60  thf('15', plain,
% 0.35/0.60      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.35/0.60         (((X12) = (X8))
% 0.35/0.60          | ((X12) = (X11))
% 0.35/0.60          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.35/0.60  thf('16', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['13', '15'])).
% 0.35/0.60  thf('17', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.60  thf('18', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['12', '17'])).
% 0.35/0.60  thf('19', plain, (((sk_A) != (sk_B))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('20', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.35/0.60      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.35/0.60  thf(antisymmetry_r2_hidden, axiom,
% 0.35/0.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.60  thf('21', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.35/0.60  thf('22', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.35/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.60  thf('23', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.60      inference('clc', [status(thm)], ['7', '22'])).
% 0.35/0.60  thf('24', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.60  thf('25', plain, (((sk_A) = (sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.60  thf('26', plain, (((sk_A) != (sk_B))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('27', plain, ($false),
% 0.35/0.60      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.35/0.60  
% 0.35/0.60  % SZS output end Refutation
% 0.35/0.60  
% 0.35/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
