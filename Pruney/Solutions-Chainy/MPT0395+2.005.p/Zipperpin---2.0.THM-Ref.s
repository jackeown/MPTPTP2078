%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4HEwwpw8X

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:53 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 217 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( r1_setfam_1 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_setfam_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r1_tarski @ ( sk_C @ X18 @ X17 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4HEwwpw8X
% 0.16/0.39  % Computer   : n025.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 12:41:21 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 38 iterations in 0.022s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.25/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.52  thf(t17_setfam_1, conjecture,
% 0.25/0.52    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.25/0.52  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(d2_setfam_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.25/0.52       ( ![C:$i]:
% 0.25/0.52         ( ~( ( r2_hidden @ C @ A ) & 
% 0.25/0.52              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.25/0.52  thf('1', plain,
% 0.25/0.52      (![X17 : $i, X18 : $i]:
% 0.25/0.52         ((r1_setfam_1 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X17))),
% 0.25/0.52      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.25/0.52  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(l32_xboole_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.52  thf('3', plain,
% 0.25/0.52      (![X9 : $i, X11 : $i]:
% 0.25/0.52         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.25/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.25/0.52  thf('4', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.52  thf(t48_xboole_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.25/0.52  thf('5', plain,
% 0.25/0.52      (![X13 : $i, X14 : $i]:
% 0.25/0.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.25/0.52           = (k3_xboole_0 @ X13 @ X14))),
% 0.25/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.52  thf('6', plain,
% 0.25/0.52      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.25/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.25/0.52  thf(t3_boole, axiom,
% 0.25/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.25/0.52  thf('7', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.25/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.52  thf('8', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.25/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.52  thf(d4_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.25/0.52       ( ![D:$i]:
% 0.25/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.25/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.25/0.52          | (r2_hidden @ X4 @ X2)
% 0.25/0.52          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.25/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.25/0.52  thf('10', plain,
% 0.25/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.25/0.52         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.25/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.25/0.52  thf('11', plain,
% 0.25/0.52      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.25/0.52      inference('sup-', [status(thm)], ['8', '10'])).
% 0.25/0.52  thf('12', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r1_setfam_1 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '11'])).
% 0.25/0.52  thf(d10_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.25/0.52  thf('13', plain,
% 0.25/0.52      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.25/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.25/0.52  thf('14', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.25/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.25/0.52  thf('15', plain,
% 0.25/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.25/0.52         ((r1_setfam_1 @ X17 @ X18)
% 0.25/0.52          | ~ (r2_hidden @ X19 @ X18)
% 0.25/0.52          | ~ (r1_tarski @ (sk_C @ X18 @ X17) @ X19))),
% 0.25/0.52      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.25/0.52  thf('16', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.25/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.52  thf('17', plain,
% 0.25/0.52      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.25/0.52      inference('sup-', [status(thm)], ['12', '16'])).
% 0.25/0.52  thf('18', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.25/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.25/0.52  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
