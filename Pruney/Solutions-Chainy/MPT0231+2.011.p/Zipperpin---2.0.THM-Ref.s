%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R08rkJ2IaC

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 303 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 = X52 )
      | ~ ( r1_tarski @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X48 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ ( k1_tarski @ X46 ) )
      | ( X45 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,(
    ! [X46: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ( X53 = X52 )
      | ~ ( r1_tarski @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X46: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X46 ) ) ),
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
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R08rkJ2IaC
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:17:15 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 48 iterations in 0.032s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.51  thf(t26_zfmisc_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.23/0.51       ( ( A ) = ( C ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.51        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.23/0.51          ( ( A ) = ( C ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.23/0.51  thf('0', plain, (((sk_A) != (sk_C_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k1_tarski @ sk_C_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(l3_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.23/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X44 : $i, X45 : $i]:
% 0.23/0.51         (((X45) = (k1_tarski @ X44))
% 0.23/0.51          | ((X45) = (k1_xboole_0))
% 0.23/0.51          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.23/0.51        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(t12_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X47 : $i, X48 : $i]:
% 0.23/0.51         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X48))),
% 0.23/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_1))
% 0.23/0.51        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(t6_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.23/0.51       ( ( A ) = ( B ) ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X52 : $i, X53 : $i]:
% 0.23/0.51         (((X53) = (X52))
% 0.23/0.51          | ~ (r1_tarski @ (k1_tarski @ X53) @ (k1_tarski @ X52)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain, (((sk_A) != (sk_C_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('9', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X47 : $i, X48 : $i]:
% 0.23/0.51         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X48))),
% 0.23/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.23/0.51  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.23/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf(t28_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X10 : $i, X11 : $i]:
% 0.23/0.51         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X45 : $i, X46 : $i]:
% 0.23/0.51         ((r1_tarski @ X45 @ (k1_tarski @ X46)) | ((X45) != (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X46 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X46))),
% 0.23/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X10 : $i, X11 : $i]:
% 0.23/0.51         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['13', '14', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X52 : $i, X53 : $i]:
% 0.23/0.51         (((X53) = (X52))
% 0.23/0.51          | ~ (r1_tarski @ (k1_tarski @ X53) @ (k1_tarski @ X52)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X46 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X46))),
% 0.23/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.51  thf('23', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.51  thf('24', plain, (((sk_A) != (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['0', '23'])).
% 0.23/0.51  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
