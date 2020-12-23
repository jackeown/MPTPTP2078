%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qIzNeSU1tM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  55 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  157 ( 348 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X11 @ X12 ) @ ( sk_D_1 @ X11 @ X12 ) ) @ X12 )
      | ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qIzNeSU1tM
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:45:55 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 25 iterations in 0.023s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.23/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(t7_xboole_0, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X10 : $i]:
% 0.23/0.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.23/0.50  thf(d3_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.50           ( ![C:$i,D:$i]:
% 0.23/0.50             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.23/0.50               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]:
% 0.23/0.50         ((r2_hidden @ 
% 0.23/0.50           (k4_tarski @ (sk_C_1 @ X11 @ X12) @ (sk_D_1 @ X11 @ X12)) @ X12)
% 0.23/0.50          | (r1_tarski @ X12 @ X11)
% 0.23/0.50          | ~ (v1_relat_1 @ X12))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.23/0.50  thf(t56_relat_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.23/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( v1_relat_1 @ A ) =>
% 0.23/0.50          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.23/0.50            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X16 : $i, X17 : $i]: ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i]: (~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('5', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.23/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf(d3_tarski, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.50          | (r2_hidden @ X0 @ X2)
% 0.23/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '7'])).
% 0.23/0.50  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('10', plain, (![X0 : $i]: (r2_hidden @ (sk_B @ sk_A) @ X0)),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf(d5_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.23/0.50       ( ![D:$i]:
% 0.23/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X8 @ X7)
% 0.23/0.50          | ~ (r2_hidden @ X8 @ X6)
% 0.23/0.50          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X8 @ X6)
% 0.23/0.50          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.50  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ (sk_B @ sk_A) @ X0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.23/0.50  thf('14', plain, (![X0 : $i]: (r2_hidden @ (sk_B @ sk_A) @ X0)),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf('15', plain, ($false), inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
