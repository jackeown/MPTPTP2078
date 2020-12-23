%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WjaXu7hDIm

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 133 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_setfam_1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','8'])).

thf('10',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WjaXu7hDIm
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 21 iterations in 0.018s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.44  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(t7_xboole_0, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.44          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.44      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.44  thf(t21_setfam_1, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.44  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d2_setfam_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.44       ( ![C:$i]:
% 0.21/0.44         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.44              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.44         ((r2_hidden @ (sk_D_1 @ X8 @ X9) @ X9)
% 0.21/0.44          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.44          | ~ (r1_setfam_1 @ X10 @ X9))),
% 0.21/0.44      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.44          | (r2_hidden @ (sk_D_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.44  thf(t3_boole, axiom,
% 0.21/0.44    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.44  thf('4', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.44      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.44  thf(d5_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.44       ( ![D:$i]:
% 0.21/0.44         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.44           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.44          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.44          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.44      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.44          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.44      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.44  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('condensation', [status(thm)], ['7'])).
% 0.21/0.44  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.21/0.44      inference('clc', [status(thm)], ['3', '8'])).
% 0.21/0.44  thf('10', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.44  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('12', plain, ($false),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
