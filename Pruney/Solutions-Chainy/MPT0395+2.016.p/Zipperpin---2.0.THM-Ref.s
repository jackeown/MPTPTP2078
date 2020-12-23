%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQ7XvHzXya

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:54 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 296 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_setfam_1 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_setfam_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r1_tarski @ ( sk_C @ X15 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQ7XvHzXya
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:09:03 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 78 iterations in 0.046s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.47  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.18/0.47  thf(t17_setfam_1, conjecture,
% 0.18/0.47    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.18/0.47  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(l32_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.47  thf('2', plain,
% 0.18/0.47      (![X6 : $i, X8 : $i]:
% 0.18/0.47         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.47  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.47  thf(d2_setfam_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.18/0.47       ( ![C:$i]:
% 0.18/0.47         ( ~( ( r2_hidden @ C @ A ) & 
% 0.18/0.47              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.18/0.47  thf('4', plain,
% 0.18/0.47      (![X14 : $i, X15 : $i]:
% 0.18/0.47         ((r1_setfam_1 @ X14 @ X15) | (r2_hidden @ (sk_C @ X15 @ X14) @ X14))),
% 0.18/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.18/0.47  thf(d5_xboole_0, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.18/0.47       ( ![D:$i]:
% 0.18/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.47          | (r2_hidden @ X0 @ X2)
% 0.18/0.47          | (r2_hidden @ X0 @ X3)
% 0.18/0.47          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.18/0.47          | (r2_hidden @ X0 @ X2)
% 0.18/0.47          | ~ (r2_hidden @ X0 @ X1))),
% 0.18/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.18/0.47  thf('7', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         ((r1_setfam_1 @ X0 @ X1)
% 0.18/0.47          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.18/0.47          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.18/0.47  thf('8', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.18/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.18/0.47          | (r1_setfam_1 @ sk_A @ X0))),
% 0.18/0.47      inference('sup+', [status(thm)], ['3', '7'])).
% 0.18/0.47  thf(t3_boole, axiom,
% 0.18/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.47  thf('9', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.18/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.47  thf(t36_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.18/0.47  thf('10', plain,
% 0.18/0.47      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.18/0.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.18/0.47  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.18/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.18/0.47  thf('12', plain,
% 0.18/0.47      (![X6 : $i, X8 : $i]:
% 0.18/0.47         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.47  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.47  thf('14', plain,
% 0.18/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.18/0.47          | ~ (r2_hidden @ X4 @ X2)
% 0.18/0.47          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.47  thf('15', plain,
% 0.18/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.18/0.47          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.18/0.47  thf('16', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['13', '15'])).
% 0.18/0.47  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.18/0.47      inference('condensation', [status(thm)], ['16'])).
% 0.18/0.47  thf('18', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         ((r1_setfam_1 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.18/0.47      inference('clc', [status(thm)], ['8', '17'])).
% 0.18/0.47  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.18/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.18/0.47  thf('20', plain,
% 0.18/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.47         ((r1_setfam_1 @ X14 @ X15)
% 0.18/0.47          | ~ (r2_hidden @ X16 @ X15)
% 0.18/0.47          | ~ (r1_tarski @ (sk_C @ X15 @ X14) @ X16))),
% 0.18/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.18/0.47  thf('21', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.47  thf('22', plain,
% 0.18/0.47      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.18/0.47      inference('sup-', [status(thm)], ['18', '21'])).
% 0.18/0.47  thf('23', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.18/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.18/0.47  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
