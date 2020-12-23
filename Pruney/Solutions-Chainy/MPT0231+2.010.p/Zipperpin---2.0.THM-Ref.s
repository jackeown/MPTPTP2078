%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jH0dlyc0v8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 303 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 = X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k1_tarski @ X39 ) )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,(
    ! [X39: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','18'])).

thf('20',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 = X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X39: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('23',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jH0dlyc0v8
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 44 iterations in 0.028s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(t26_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.51       ( ( A ) = ( C ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.51          ( ( A ) = ( C ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.21/0.51  thf('0', plain, (((sk_A) != (sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l3_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X37 : $i, X38 : $i]:
% 0.21/0.51         (((X38) = (k1_tarski @ X37))
% 0.21/0.51          | ((X38) = (k1_xboole_0))
% 0.21/0.51          | ~ (r1_tarski @ X38 @ (k1_tarski @ X37)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(t12_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X40 : $i, X41 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_tarski @ X40) @ (k2_tarski @ X40 @ X41))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.21/0.51        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf(t6_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.51       ( ( A ) = ( B ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X42 : $i, X43 : $i]:
% 0.21/0.51         (((X43) = (X42))
% 0.21/0.51          | ~ (r1_tarski @ (k1_tarski @ X43) @ (k1_tarski @ X42)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_A) = (sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, (((sk_A) != (sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X40 : $i, X41 : $i]:
% 0.21/0.51         (r1_tarski @ (k1_tarski @ X40) @ (k2_tarski @ X40 @ X41))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.51  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X38 : $i, X39 : $i]:
% 0.21/0.51         ((r1_tarski @ X38 @ (k1_tarski @ X39)) | ((X38) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X39 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X39))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X42 : $i, X43 : $i]:
% 0.21/0.51         (((X43) = (X42))
% 0.21/0.51          | ~ (r1_tarski @ (k1_tarski @ X43) @ (k1_tarski @ X42)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X39 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X39))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('23', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, (((sk_A) != (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '23'])).
% 0.21/0.51  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
