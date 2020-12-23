%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wn9I1ryjQH

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 169 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(t59_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r2_xboole_0 @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t59_xboole_1])).

thf('0',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t56_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X5 )
      | ( r2_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_xboole_0 @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wn9I1ryjQH
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:52:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 13 iterations in 0.006s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.44  thf(t59_xboole_1, conjecture,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.22/0.44       ( r2_xboole_0 @ A @ C ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.44        ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.22/0.44          ( r2_xboole_0 @ A @ C ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t59_xboole_1])).
% 0.22/0.44  thf('0', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('1', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('2', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(d8_xboole_0, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.44       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.44  thf('4', plain,
% 0.22/0.44      (![X0 : $i, X2 : $i]:
% 0.22/0.44         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.44      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.44  thf('5', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.44  thf(t56_xboole_1, axiom,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( r2_xboole_0 @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.22/0.44       ( r2_xboole_0 @ A @ C ) ))).
% 0.22/0.44  thf('6', plain,
% 0.22/0.44      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.44         (~ (r2_xboole_0 @ X3 @ X4)
% 0.22/0.44          | ~ (r2_xboole_0 @ X4 @ X5)
% 0.22/0.44          | (r2_xboole_0 @ X3 @ X5))),
% 0.22/0.44      inference('cnf', [status(esa)], [t56_xboole_1])).
% 0.22/0.44  thf('7', plain,
% 0.22/0.44      (![X0 : $i]:
% 0.22/0.44         (((sk_A) = (sk_B))
% 0.22/0.44          | (r2_xboole_0 @ sk_A @ X0)
% 0.22/0.44          | ~ (r2_xboole_0 @ sk_B @ X0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.44  thf('8', plain, (((r2_xboole_0 @ sk_A @ sk_C) | ((sk_A) = (sk_B)))),
% 0.22/0.44      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.44  thf('9', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('10', plain, (((sk_A) = (sk_B))),
% 0.22/0.44      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.44  thf('11', plain, ((r2_xboole_0 @ sk_A @ sk_C)),
% 0.22/0.44      inference('demod', [status(thm)], ['1', '10'])).
% 0.22/0.44  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
