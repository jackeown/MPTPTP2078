%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNt4vFzvVb

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 255 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X67: $i,X68: $i] :
      ( ( X68 != X67 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X68 ) @ ( k1_tarski @ X67 ) )
       != ( k1_tarski @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X67: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X67 ) @ ( k1_tarski @ X67 ) )
     != ( k1_tarski @ X67 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNt4vFzvVb
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:37:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 22 iterations in 0.016s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.45  thf(t49_zfmisc_1, conjecture,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i,B:$i]:
% 0.18/0.45        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t7_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.18/0.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.45  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.18/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.18/0.45  thf(d10_xboole_0, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X2 : $i, X4 : $i]:
% 0.18/0.45         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.18/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.18/0.45        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.45  thf('5', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.18/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.45  thf('6', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.18/0.45  thf(t20_zfmisc_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.18/0.45         ( k1_tarski @ A ) ) <=>
% 0.18/0.45       ( ( A ) != ( B ) ) ))).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      (![X67 : $i, X68 : $i]:
% 0.18/0.45         (((X68) != (X67))
% 0.18/0.45          | ((k4_xboole_0 @ (k1_tarski @ X68) @ (k1_tarski @ X67))
% 0.18/0.45              != (k1_tarski @ X68)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X67 : $i]:
% 0.18/0.45         ((k4_xboole_0 @ (k1_tarski @ X67) @ (k1_tarski @ X67))
% 0.18/0.45           != (k1_tarski @ X67))),
% 0.18/0.45      inference('simplify', [status(thm)], ['7'])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.18/0.45      inference('sup-', [status(thm)], ['6', '8'])).
% 0.18/0.45  thf('10', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.18/0.45  thf(t4_boole, axiom,
% 0.18/0.45    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.45  thf('11', plain,
% 0.18/0.45      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [t4_boole])).
% 0.18/0.45  thf('12', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.18/0.45  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.45      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.18/0.45  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
