%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.43HrtxQUD1

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
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

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ( r1_xboole_0 @ ( k2_tarski @ X51 @ X53 ) @ X52 )
      | ( r2_hidden @ X53 @ X52 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.43HrtxQUD1
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 171 iterations in 0.093s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(t144_zfmisc_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.36/0.55          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.55        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.36/0.55             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.36/0.55  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t57_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.36/0.55          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.36/0.55         ((r2_hidden @ X51 @ X52)
% 0.36/0.55          | (r1_xboole_0 @ (k2_tarski @ X51 @ X53) @ X52)
% 0.36/0.55          | (r2_hidden @ X53 @ X52))),
% 0.36/0.55      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.36/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r2_hidden @ X1 @ X0)
% 0.36/0.55          | (r2_hidden @ X2 @ X0)
% 0.36/0.55          | (r1_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf(t88_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_xboole_0 @ A @ B ) =>
% 0.36/0.55       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13) = (X12))
% 0.36/0.55          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.36/0.55  thf(t40_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.36/0.55           = (k4_xboole_0 @ X6 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r2_hidden @ X1 @ X2)
% 0.36/0.55          | (r2_hidden @ X0 @ X2)
% 0.36/0.55          | ((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((((sk_C) != (sk_C))
% 0.36/0.55        | (r2_hidden @ sk_B @ sk_C)
% 0.36/0.55        | (r2_hidden @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.36/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.55  thf('11', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.36/0.55      inference('clc', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
