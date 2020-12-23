%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ji3k1xUyj5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 252 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t79_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
        = ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) )
        = ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ji3k1xUyj5
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 1029 iterations in 0.436s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(t79_zfmisc_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) =>
% 0.71/0.90       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i]:
% 0.71/0.90        ( ( r1_tarski @ A @ B ) =>
% 0.71/0.90          ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t79_zfmisc_1])).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (~ (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d3_tarski, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) <=>
% 0.71/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X3 : $i, X5 : $i]:
% 0.71/0.90         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.90  thf(d1_zfmisc_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.71/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X14 @ X13)
% 0.71/0.90          | (r1_tarski @ X14 @ X12)
% 0.71/0.90          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X12 : $i, X14 : $i]:
% 0.71/0.90         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['2'])).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.71/0.90          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['1', '3'])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.71/0.90          | ((k3_xboole_0 @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.71/0.90              = (sk_C @ X1 @ (k1_zfmisc_1 @ X0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.71/0.90          | ((k3_xboole_0 @ X0 @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)))
% 0.71/0.90              = (sk_C @ X1 @ (k1_zfmisc_1 @ X0))))),
% 0.71/0.90      inference('demod', [status(thm)], ['6', '7'])).
% 0.71/0.90  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t108_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k3_xboole_0 @ X6 @ X8) @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.71/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X11 @ X12)
% 0.71/0.90          | (r2_hidden @ X11 @ X13)
% 0.71/0.90          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X11 : $i, X12 : $i]:
% 0.71/0.90         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 0.71/0.90      inference('simplify', [status(thm)], ['12'])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (r2_hidden @ (k3_xboole_0 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['11', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.71/0.90           (k1_zfmisc_1 @ sk_B))
% 0.71/0.90          | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['8', '14'])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X3 : $i, X5 : $i]:
% 0.71/0.90         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.71/0.90        | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf('18', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.71/0.90      inference('simplify', [status(thm)], ['17'])).
% 0.71/0.90  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
