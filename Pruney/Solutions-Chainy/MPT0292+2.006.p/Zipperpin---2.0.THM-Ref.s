%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gAQjly7Igo

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 226 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( r1_tarski @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X15 ) @ ( k3_tarski @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_tarski @ X8 @ X6 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gAQjly7Igo
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 51 iterations in 0.030s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(t99_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.49  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('1', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t80_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X12 : $i]: (r1_tarski @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t95_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ X15) @ (k3_tarski @ X16))
% 0.21/0.49          | ~ (r1_tarski @ X15 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X0)) @ 
% 0.21/0.49          (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(l51_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.49  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.49  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.21/0.49          | ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t94_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.21/0.49       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.21/0.49          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.49  thf(d1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.49          | (r1_tarski @ X8 @ X6)
% 0.21/0.49          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X6 : $i, X8 : $i]:
% 0.21/0.49         ((r1_tarski @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.21/0.49          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.21/0.49          | ~ (r1_tarski @ (sk_C_1 @ X14 @ X13) @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '17'])).
% 0.21/0.49  thf('19', plain, (((sk_A) != (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.49  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
