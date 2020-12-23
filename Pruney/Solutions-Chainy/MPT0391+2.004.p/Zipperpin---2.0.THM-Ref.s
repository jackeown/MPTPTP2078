%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IicfFpHeGu

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 277 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_setfam_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( k1_setfam_1 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IicfFpHeGu
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(t9_setfam_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.47       ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.47          ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t9_setfam_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t8_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.21/0.47       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X9 @ X10)
% 0.21/0.47          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.47          | (r1_tarski @ (k1_setfam_1 @ X10) @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.47  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t86_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.47       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.47          | ~ (r1_xboole_0 @ X6 @ X8)
% 0.21/0.47          | (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.21/0.47          | ~ (r1_tarski @ sk_A @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.47  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf(t106_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.47       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.47          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X3 @ X5)
% 0.21/0.47          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '19'])).
% 0.21/0.47  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
