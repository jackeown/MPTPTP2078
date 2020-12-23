%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DZOoaBiBlg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  86 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 504 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,
    ( ( sk_B = sk_C )
    | ( r2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('5',plain,
    ( ( sk_B = sk_C )
    | ~ ( r2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( k2_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['12','17'])).

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
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['5','22','23','24'])).

thf('26',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','25'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DZOoaBiBlg
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:29:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 34 iterations in 0.018s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(t58_xboole_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.46       ( r2_xboole_0 @ A @ C ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.46        ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.46          ( r2_xboole_0 @ A @ C ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t58_xboole_1])).
% 0.18/0.46  thf('0', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(d8_xboole_0, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.18/0.46       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X2 : $i, X4 : $i]:
% 0.18/0.46         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.46  thf('3', plain, ((((sk_B) = (sk_C)) | (r2_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.46  thf(antisymmetry_r2_xboole_0, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.18/0.46      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.18/0.46  thf('5', plain, ((((sk_B) = (sk_C)) | ~ (r2_xboole_0 @ sk_C @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.46  thf('6', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(l32_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X6 : $i, X8 : $i]:
% 0.18/0.46         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.46  thf('8', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.18/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf(t39_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i]:
% 0.18/0.46         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.18/0.46           = (k2_xboole_0 @ X13 @ X14))),
% 0.18/0.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.18/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf(t1_boole, axiom,
% 0.18/0.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.46  thf('11', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.18/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.18/0.46  thf('12', plain, (((sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('13', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.46  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf(t10_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X9 @ X10)
% 0.18/0.46          | (r1_tarski @ X9 @ (k2_xboole_0 @ X11 @ X10)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.46  thf('18', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.18/0.46      inference('sup+', [status(thm)], ['12', '17'])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      (![X2 : $i, X4 : $i]:
% 0.18/0.46         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.46  thf('20', plain, ((((sk_A) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.46  thf('21', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('22', plain, (((sk_A) = (sk_C))),
% 0.18/0.46      inference('clc', [status(thm)], ['20', '21'])).
% 0.18/0.46  thf('23', plain, (((sk_A) = (sk_C))),
% 0.18/0.46      inference('clc', [status(thm)], ['20', '21'])).
% 0.18/0.46  thf('24', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('25', plain, (((sk_B) = (sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['5', '22', '23', '24'])).
% 0.18/0.46  thf('26', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.18/0.46      inference('demod', [status(thm)], ['0', '25'])).
% 0.18/0.46  thf(irreflexivity_r2_xboole_0, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.18/0.46  thf('27', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.18/0.46      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.18/0.46  thf('28', plain, ($false), inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
