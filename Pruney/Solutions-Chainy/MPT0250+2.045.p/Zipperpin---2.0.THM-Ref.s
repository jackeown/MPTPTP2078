%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rK7trk1o8v

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  160 ( 205 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rK7trk1o8v
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:57:22 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 57 iterations in 0.017s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.49  thf(t45_zfmisc_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.23/0.49       ( r2_hidden @ A @ B ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i]:
% 0.23/0.49        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.23/0.49          ( r2_hidden @ A @ B ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.23/0.49  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      ((r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.23/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf(t12_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (((k2_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.23/0.49         = (sk_B))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.23/0.49         = (sk_B))),
% 0.23/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.49  thf(t7_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.23/0.49           = (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.49  thf('11', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.23/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.23/0.49  thf(l1_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i]:
% 0.23/0.49         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 0.23/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.49  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.23/0.49      inference('sup+', [status(thm)], ['11', '16'])).
% 0.23/0.49  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
