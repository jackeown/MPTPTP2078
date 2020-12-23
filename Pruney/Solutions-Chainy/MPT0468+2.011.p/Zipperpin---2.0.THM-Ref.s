%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eVmZ0HAywl

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 ( 227 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ sk_A ) ),
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

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_2 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_2 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_B @ sk_A ) @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('sup-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eVmZ0HAywl
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 23 iterations in 0.018s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(t7_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.49  thf(d3_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.49               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X6)
% 0.21/0.49          | (r1_tarski @ X6 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.49  thf(t56_relat_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ A ) =>
% 0.21/0.49          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.49            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]: (~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | (r2_hidden @ X0 @ X2)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.49  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, (![X0 : $i]: (r2_hidden @ (sk_B @ sk_A) @ X0)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(d4_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X14 @ X13)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_2 @ X14 @ X12)) @ X12)
% 0.21/0.49          | ((X13) != (k1_relat_1 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X12 : $i, X14 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_2 @ X14 @ X12)) @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (r2_hidden @ 
% 0.21/0.49          (k4_tarski @ (sk_B @ sk_A) @ (sk_D_2 @ (sk_B @ sk_A) @ X0)) @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, ($false), inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
