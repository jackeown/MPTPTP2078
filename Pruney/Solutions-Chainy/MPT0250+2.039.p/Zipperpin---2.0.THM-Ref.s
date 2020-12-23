%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Urrb3PFwwL

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:52 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 186 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ ( k2_tarski @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Urrb3PFwwL
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 11:38:51 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.25/0.39  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 57 iterations in 0.030s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(t45_zfmisc_1, conjecture,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.35/0.52       ( r2_hidden @ A @ B ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i]:
% 0.35/0.52        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.35/0.52          ( r2_hidden @ A @ B ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.35/0.52  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      ((r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.35/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.35/0.52  thf(d10_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X2 : $i, X4 : $i]:
% 0.35/0.52         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.35/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.35/0.52        | ((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.52  thf(t7_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.35/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.52  thf('7', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.35/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.52  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.35/0.52      inference('sup+', [status(thm)], ['7', '10'])).
% 0.35/0.52  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(t38_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.35/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.53         ((r2_hidden @ X15 @ X16)
% 0.35/0.53          | ~ (r1_tarski @ (k2_tarski @ X15 @ X17) @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.53  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
