%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vvshlwvnY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 317 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t56_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_xboole_0 @ A @ B )
          & ( r2_xboole_0 @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t56_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('2',plain,(
    ~ ( r2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','16','17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('23',plain,
    ( ( sk_A = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['2','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vvshlwvnY
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 39 iterations in 0.018s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t56_xboole_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r2_xboole_0 @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.20/0.48       ( r2_xboole_0 @ A @ C ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( r2_xboole_0 @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.20/0.48          ( r2_xboole_0 @ A @ C ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t56_xboole_1])).
% 0.20/0.48  thf('0', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(antisymmetry_r2_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.20/0.48  thf('2', plain, (~ (r2_xboole_0 @ sk_C @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.48  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.48  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(l32_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X7 : $i, X9 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('10', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(t39_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.20/0.48           = (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf(t1_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('15', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.48  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf('18', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '16', '17'])).
% 0.20/0.48  thf(t11_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ X10 @ X11)
% 0.20/0.48          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i]:
% 0.20/0.48         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.48  thf('23', plain, ((((sk_A) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain, (((sk_A) = (sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '25', '26'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
