%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hjN5qwcITY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  162 ( 214 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ X50 )
      | ( r1_xboole_0 @ ( k2_tarski @ X49 @ X51 ) @ X50 )
      | ( r2_hidden @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hjN5qwcITY
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:39:23 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 171 iterations in 0.055s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(t144_zfmisc_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.23/0.49          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.23/0.49             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.23/0.49  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t57_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.23/0.49          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.23/0.49         ((r2_hidden @ X49 @ X50)
% 0.23/0.49          | (r1_xboole_0 @ (k2_tarski @ X49 @ X51) @ X50)
% 0.23/0.49          | (r2_hidden @ X51 @ X50))),
% 0.23/0.49      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.23/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((r2_hidden @ X1 @ X0)
% 0.23/0.49          | (r2_hidden @ X2 @ X0)
% 0.23/0.49          | (r1_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf(t88_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_xboole_0 @ A @ B ) =>
% 0.23/0.49       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X12 : $i, X13 : $i]:
% 0.23/0.49         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13) = (X12))
% 0.23/0.49          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.23/0.49      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.23/0.49  thf(t40_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i]:
% 0.23/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.23/0.49           = (k4_xboole_0 @ X6 @ X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X12 : $i, X13 : $i]:
% 0.23/0.49         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.23/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((r2_hidden @ X1 @ X2)
% 0.23/0.49          | (r2_hidden @ X0 @ X2)
% 0.23/0.49          | ((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      ((((sk_C) != (sk_C))
% 0.23/0.49        | (r2_hidden @ sk_B @ sk_C)
% 0.23/0.49        | (r2_hidden @ sk_A @ sk_C))),
% 0.23/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.49  thf('10', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.23/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.49  thf('11', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('12', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.23/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.23/0.49  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
