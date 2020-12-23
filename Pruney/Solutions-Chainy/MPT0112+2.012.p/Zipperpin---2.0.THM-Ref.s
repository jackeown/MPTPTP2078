%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f3y36mHtnA

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 192 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t105_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ A @ B )
          & ( ( k4_xboole_0 @ B @ A )
            = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t105_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('2',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

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
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('14',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f3y36mHtnA
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 18 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(t105_xboole_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.46          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.46             ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t105_xboole_1])).
% 0.20/0.46  thf('0', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t6_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.46          ( ![C:$i]:
% 0.20/0.46            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.46  thf('2', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(l32_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf(t28_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i]:
% 0.20/0.46         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.46  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf(d4_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.46       ( ![D:$i]:
% 0.20/0.46         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.46           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.46          | (r2_hidden @ X4 @ X2)
% 0.20/0.46          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.46         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.46  thf('12', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (r2_xboole_0 @ X6 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.46  thf('14', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
