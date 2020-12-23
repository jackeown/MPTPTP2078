%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xb6cnQj2SZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 177 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t17_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_setfam_1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t17_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_setfam_1 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_setfam_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r1_tarski @ ( sk_C @ X14 @ X13 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xb6cnQj2SZ
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 15:02:57 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 22 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(t17_setfam_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.47              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         ((r1_setfam_1 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.47  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t28_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.47  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(d4_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.47          | (r2_hidden @ X4 @ X2)
% 0.21/0.47          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.47         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_setfam_1 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('10', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.21/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         ((r1_setfam_1 @ X13 @ X14)
% 0.21/0.47          | ~ (r2_hidden @ X15 @ X14)
% 0.21/0.47          | ~ (r1_tarski @ (sk_C @ X14 @ X13) @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '12'])).
% 0.21/0.47  thf('14', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.21/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.47  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
