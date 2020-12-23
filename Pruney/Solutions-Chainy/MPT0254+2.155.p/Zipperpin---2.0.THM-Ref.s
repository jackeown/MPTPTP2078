%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b4dR8fRxEC

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 137 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('3',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(l20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l20_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference('sup-',[status(thm)],['11','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b4dR8fRxEC
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:26:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 15 iterations in 0.010s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.45  thf('0', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf(t49_zfmisc_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t15_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.45       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X2 : $i, X3 : $i]:
% 0.19/0.45         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.45  thf('4', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.45  thf(l20_zfmisc_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.19/0.45       ( r2_hidden @ A @ B ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X6 : $i, X7 : $i]:
% 0.19/0.45         ((r2_hidden @ X6 @ X7)
% 0.19/0.45          | ~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X6) @ X7) @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [l20_zfmisc_1])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.19/0.45          | (r2_hidden @ sk_A @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf('7', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf(t12_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.19/0.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.45  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.19/0.45      inference('demod', [status(thm)], ['6', '9'])).
% 0.19/0.45  thf('11', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '10'])).
% 0.19/0.45  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.45  thf('12', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.19/0.45      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.45  thf(l24_zfmisc_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (~ (r1_xboole_0 @ (k1_tarski @ X8) @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.45  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.45  thf('15', plain, ($false), inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
