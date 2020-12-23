%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmkmhIhuCJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 250 expanded)
%              Number of equality atoms :    8 (   9 expanded)
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k1_zfmisc_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmkmhIhuCJ
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 16:58:23 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.30/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.52  % Solved by: fo/fo7.sh
% 1.30/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.52  % done 1239 iterations in 1.059s
% 1.30/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.52  % SZS output start Refutation
% 1.30/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.52  thf(t79_zfmisc_1, conjecture,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( r1_tarski @ A @ B ) =>
% 1.30/1.52       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.30/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.52    (~( ![A:$i,B:$i]:
% 1.30/1.52        ( ( r1_tarski @ A @ B ) =>
% 1.30/1.52          ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 1.30/1.52    inference('cnf.neg', [status(esa)], [t79_zfmisc_1])).
% 1.30/1.52  thf('0', plain,
% 1.30/1.52      (~ (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf(t12_xboole_1, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.30/1.52  thf('2', plain,
% 1.30/1.52      (![X9 : $i, X10 : $i]:
% 1.30/1.52         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.30/1.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.30/1.52  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.30/1.52      inference('sup-', [status(thm)], ['1', '2'])).
% 1.30/1.52  thf(commutativity_k2_xboole_0, axiom,
% 1.30/1.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.30/1.52  thf('4', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.52  thf(d3_tarski, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.52  thf('5', plain,
% 1.30/1.52      (![X3 : $i, X5 : $i]:
% 1.30/1.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.30/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.52  thf(d1_zfmisc_1, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.30/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.30/1.52  thf('6', plain,
% 1.30/1.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.30/1.52         (~ (r2_hidden @ X14 @ X13)
% 1.30/1.52          | (r1_tarski @ X14 @ X12)
% 1.30/1.52          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 1.30/1.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.30/1.52  thf('7', plain,
% 1.30/1.52      (![X12 : $i, X14 : $i]:
% 1.30/1.52         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['6'])).
% 1.30/1.52  thf('8', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 1.30/1.52          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['5', '7'])).
% 1.30/1.52  thf(t10_xboole_1, axiom,
% 1.30/1.52    (![A:$i,B:$i,C:$i]:
% 1.30/1.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.30/1.52  thf('9', plain,
% 1.30/1.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.30/1.52         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 1.30/1.52      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.30/1.52  thf('10', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 1.30/1.52          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 1.30/1.52             (k2_xboole_0 @ X2 @ X0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.52  thf('11', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.52         ((r1_tarski @ (sk_C @ X2 @ (k1_zfmisc_1 @ X1)) @ 
% 1.30/1.52           (k2_xboole_0 @ X1 @ X0))
% 1.30/1.52          | (r1_tarski @ (k1_zfmisc_1 @ X1) @ X2))),
% 1.30/1.52      inference('sup+', [status(thm)], ['4', '10'])).
% 1.30/1.52  thf('12', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((r1_tarski @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 1.30/1.52          | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0))),
% 1.30/1.52      inference('sup+', [status(thm)], ['3', '11'])).
% 1.30/1.52  thf('13', plain,
% 1.30/1.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.30/1.52         (~ (r1_tarski @ X11 @ X12)
% 1.30/1.52          | (r2_hidden @ X11 @ X13)
% 1.30/1.52          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 1.30/1.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.30/1.52  thf('14', plain,
% 1.30/1.52      (![X11 : $i, X12 : $i]:
% 1.30/1.52         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 1.30/1.52      inference('simplify', [status(thm)], ['13'])).
% 1.30/1.52  thf('15', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0)
% 1.30/1.52          | (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 1.30/1.52             (k1_zfmisc_1 @ sk_B)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['12', '14'])).
% 1.30/1.52  thf('16', plain,
% 1.30/1.52      (![X3 : $i, X5 : $i]:
% 1.30/1.52         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.30/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.52  thf('17', plain,
% 1.30/1.52      (((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 1.30/1.52        | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['15', '16'])).
% 1.30/1.52  thf('18', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 1.30/1.52      inference('simplify', [status(thm)], ['17'])).
% 1.30/1.52  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 1.30/1.52  
% 1.30/1.52  % SZS output end Refutation
% 1.30/1.52  
% 1.30/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
