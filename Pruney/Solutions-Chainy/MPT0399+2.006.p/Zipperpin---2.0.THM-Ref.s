%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6pf2uLR3sJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 159 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_setfam_1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6pf2uLR3sJ
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:33:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 39 iterations in 0.027s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(d1_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf(t21_setfam_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.22/0.50  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_setfam_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_D @ X8 @ X9) @ X9)
% 0.22/0.50          | ~ (r2_hidden @ X8 @ X10)
% 0.22/0.50          | ~ (r1_setfam_1 @ X10 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.50          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X4 : $i, X6 : $i]:
% 0.22/0.50         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t3_xboole_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.22/0.50      inference('clc', [status(thm)], ['4', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf('15', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('17', plain, ($false), inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
