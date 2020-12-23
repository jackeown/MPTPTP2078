%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bouezRDz96

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:26 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  274 ( 599 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t58_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_xboole_0 @ A @ B )
          & ( r1_tarski @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t58_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C ),
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
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['5','6','9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('20',plain,
    ( ( sk_A = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['20','21'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','22','23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','35'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('37',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bouezRDz96
% 0.09/0.31  % Computer   : n015.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % DateTime   : Tue Dec  1 13:24:53 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.09/0.31  % Running portfolio for 600 s
% 0.09/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.31  % Number of cores: 8
% 0.16/0.32  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 0.18/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.44  % Solved by: fo/fo7.sh
% 0.18/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.44  % done 50 iterations in 0.019s
% 0.18/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.44  % SZS output start Refutation
% 0.18/0.44  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.18/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.44  thf(t58_xboole_1, conjecture,
% 0.18/0.44    (![A:$i,B:$i,C:$i]:
% 0.18/0.44     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.44       ( r2_xboole_0 @ A @ C ) ))).
% 0.18/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.44        ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.44          ( r2_xboole_0 @ A @ C ) ) )),
% 0.18/0.44    inference('cnf.neg', [status(esa)], [t58_xboole_1])).
% 0.18/0.44  thf('0', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf(l32_xboole_1, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.44  thf('2', plain,
% 0.18/0.44      (![X6 : $i, X8 : $i]:
% 0.18/0.44         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.44  thf('3', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.18/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.44  thf(t39_xboole_1, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.44  thf('4', plain,
% 0.18/0.44      (![X13 : $i, X14 : $i]:
% 0.18/0.44         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.18/0.44           = (k2_xboole_0 @ X13 @ X14))),
% 0.18/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.18/0.44  thf('5', plain,
% 0.18/0.44      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.18/0.44      inference('sup+', [status(thm)], ['3', '4'])).
% 0.18/0.44  thf(commutativity_k2_xboole_0, axiom,
% 0.18/0.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.18/0.44  thf('6', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf('7', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf(t1_boole, axiom,
% 0.18/0.44    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.44  thf('8', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.18/0.44      inference('cnf', [status(esa)], [t1_boole])).
% 0.18/0.44  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.18/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.18/0.44  thf('10', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf('11', plain, (((sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.44      inference('demod', [status(thm)], ['5', '6', '9', '10'])).
% 0.18/0.44  thf('12', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('13', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf(d8_xboole_0, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.18/0.44       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.18/0.44  thf('14', plain,
% 0.18/0.44      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.18/0.44      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.44  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.44  thf(t1_xboole_1, axiom,
% 0.18/0.44    (![A:$i,B:$i,C:$i]:
% 0.18/0.44     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.44       ( r1_tarski @ A @ C ) ))).
% 0.18/0.44  thf('16', plain,
% 0.18/0.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.44         (~ (r1_tarski @ X10 @ X11)
% 0.18/0.44          | ~ (r1_tarski @ X11 @ X12)
% 0.18/0.44          | (r1_tarski @ X10 @ X12))),
% 0.18/0.44      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.18/0.44  thf('17', plain,
% 0.18/0.44      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.18/0.44      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.44  thf('18', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.18/0.44      inference('sup-', [status(thm)], ['12', '17'])).
% 0.18/0.44  thf('19', plain,
% 0.18/0.44      (![X2 : $i, X4 : $i]:
% 0.18/0.44         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.44      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.44  thf('20', plain, ((((sk_A) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.44      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.44  thf('21', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('22', plain, (((sk_A) = (sk_C))),
% 0.18/0.44      inference('clc', [status(thm)], ['20', '21'])).
% 0.18/0.44  thf('23', plain, (((sk_A) = (sk_C))),
% 0.18/0.44      inference('clc', [status(thm)], ['20', '21'])).
% 0.18/0.44  thf('24', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf('25', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['11', '22', '23', '24'])).
% 0.18/0.44  thf('26', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.44  thf('27', plain,
% 0.18/0.44      (![X6 : $i, X8 : $i]:
% 0.18/0.44         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.44  thf('28', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.18/0.44      inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.44  thf('29', plain,
% 0.18/0.44      (![X13 : $i, X14 : $i]:
% 0.18/0.44         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.18/0.44           = (k2_xboole_0 @ X13 @ X14))),
% 0.18/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.18/0.44  thf('30', plain,
% 0.18/0.44      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.18/0.44      inference('sup+', [status(thm)], ['28', '29'])).
% 0.18/0.44  thf('31', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.18/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.18/0.44  thf('33', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.18/0.44  thf('34', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.18/0.44  thf('35', plain, (((sk_B) = (sk_A))),
% 0.18/0.44      inference('sup+', [status(thm)], ['25', '34'])).
% 0.18/0.44  thf('36', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.18/0.44      inference('demod', [status(thm)], ['0', '35'])).
% 0.18/0.44  thf(irreflexivity_r2_xboole_0, axiom,
% 0.18/0.44    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.18/0.44  thf('37', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.18/0.44      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.18/0.44  thf('38', plain, ($false), inference('sup-', [status(thm)], ['36', '37'])).
% 0.18/0.44  
% 0.18/0.44  % SZS output end Refutation
% 0.18/0.44  
% 0.18/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
