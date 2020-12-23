%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5h8Rq9VYdf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  149 ( 176 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5h8Rq9VYdf
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 57 iterations in 0.030s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.45  thf(t45_zfmisc_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.45       ( r2_hidden @ A @ B ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.45          ( r2_hidden @ A @ B ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.21/0.45  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d10_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.45        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.45  thf(t10_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf('8', plain, (((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['3', '7'])).
% 0.21/0.45  thf(t7_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.45  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.45      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf(t69_enumset1, axiom,
% 0.21/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.21/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.45  thf(t38_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.45       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.45         ((r2_hidden @ X42 @ X43)
% 0.21/0.45          | ~ (r1_tarski @ (k2_tarski @ X42 @ X44) @ X43))),
% 0.21/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('14', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.45  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
