%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9jeF9xHhB

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 ( 310 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t7_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 )
      | ( r1_tarski @ X9 @ ( k1_setfam_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k1_tarski @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( sk_C @ X9 @ X8 ) )
      | ( r1_tarski @ X9 @ ( k1_setfam_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9jeF9xHhB
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 22 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t7_setfam_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t7_setfam_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t6_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (((X8) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ (sk_C @ X9 @ X8) @ X8)
% 0.20/0.47          | (r1_tarski @ X9 @ (k1_setfam_1 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.47  thf(l1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(t1_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.47       ( r1_tarski @ A @ C ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.47          | (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.47  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((r2_hidden @ X3 @ X4) | ~ (r1_tarski @ (k1_tarski @ X3) @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(t4_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_setfam_1 @ X6) @ X7) | ~ (r2_hidden @ X7 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C @ X0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (((X8) = (k1_xboole_0))
% 0.20/0.47          | ~ (r1_tarski @ X9 @ (sk_C @ X9 @ X8))
% 0.20/0.47          | (r1_tarski @ X9 @ (k1_setfam_1 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.47        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((((sk_A) = (k1_xboole_0))
% 0.20/0.47        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.47  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
