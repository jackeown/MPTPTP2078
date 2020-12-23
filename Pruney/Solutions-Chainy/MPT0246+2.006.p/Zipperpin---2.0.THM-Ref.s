%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybeGXMZ8lu

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  63 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 421 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('5',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_A )
      | ( X33 = sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X30: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ X32 )
        = ( k1_tarski @ X30 ) )
      | ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['14','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybeGXMZ8lu
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.48  thf(l1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X27 : $i, X28 : $i]:
% 0.21/0.48         ((r2_hidden @ X27 @ X28) | ~ (r1_tarski @ (k1_tarski @ X27) @ X28))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf(t41_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X33 : $i]: (~ (r2_hidden @ X33 @ sk_A) | ((X33) = (sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ sk_B @ X0)
% 0.21/0.48          | (r1_tarski @ sk_A @ X0)
% 0.21/0.48          | (r1_tarski @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i]:
% 0.21/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.48        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.48  thf(l33_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X30 : $i, X32 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k1_tarski @ X30) @ X32) = (k1_tarski @ X30))
% 0.21/0.48          | (r2_hidden @ X30 @ X32))),
% 0.21/0.48      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.48  thf(t38_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X0 @ X1)
% 0.21/0.48          | ((X1) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.48  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X27 : $i, X29 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('23', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ($false), inference('demod', [status(thm)], ['14', '23'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
