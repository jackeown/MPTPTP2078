%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eeKcwuBy4T

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 ( 365 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['7','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eeKcwuBy4T
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 48 iterations in 0.021s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.45  thf(t66_zfmisc_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.45          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.45             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(l32_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i]:
% 0.21/0.45         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.21/0.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.45        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.45  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.45  thf(d10_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X5 : $i, X7 : $i]:
% 0.21/0.45         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      ((~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.21/0.45        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf(t7_xboole_0, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.45          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.45  thf('9', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.45  thf(d3_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.45          | (r2_hidden @ X0 @ X2)
% 0.21/0.45          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      ((((sk_A) = (k1_xboole_0))
% 0.21/0.45        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.45  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('14', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.45  thf(d1_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.45          | ((X16) = (X13))
% 0.21/0.45          | ((X15) != (k1_tarski @ X13)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X13 : $i, X16 : $i]:
% 0.21/0.45         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.45  thf('17', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.45  thf(l1_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X24 : $i, X26 : $i]:
% 0.21/0.45         ((r1_tarski @ (k1_tarski @ X24) @ X26) | ~ (r2_hidden @ X24 @ X26))),
% 0.21/0.45      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.45  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('23', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.45  thf('24', plain, ($false), inference('demod', [status(thm)], ['7', '23'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
