%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DHrV4OwUq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  186 ( 265 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k1_tarski @ X9 ) @ ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 = X11 )
      | ( X12 = X13 )
      | ~ ( r1_tarski @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('13',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DHrV4OwUq
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 18:36:06 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 23 iterations in 0.015s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf(t12_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (r1_tarski @ (k1_tarski @ X9) @ (k2_tarski @ X9 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.50          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ (k2_tarski @ X0 @ X2)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf(t28_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.50          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.50             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.50             (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.22/0.50        | (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.22/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.50  thf(t25_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.22/0.50          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((X12) = (X11))
% 0.22/0.50          | ((X12) = (X13))
% 0.22/0.50          | ~ (r1_tarski @ (k1_tarski @ X12) @ (k2_tarski @ X11 @ X13)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.22/0.50  thf('13', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, (((sk_A) != (sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain, (((sk_A) != (sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['13', '14', '15'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
