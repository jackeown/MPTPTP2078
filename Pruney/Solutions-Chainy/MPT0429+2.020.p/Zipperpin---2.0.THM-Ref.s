%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q9HzlZEEds

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  132 ( 132 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('9',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q9HzlZEEds
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 32 iterations in 0.009s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.45  thf(t61_setfam_1, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( m1_subset_1 @
% 0.21/0.45       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( m1_subset_1 @
% 0.21/0.45          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d3_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf(t113_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X11 : $i, X12 : $i]:
% 0.21/0.45         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.45          | ((X12) != (k1_xboole_0)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.45  thf(t152_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.45      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.45  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.45  thf(t79_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.45       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X15 : $i, X16 : $i]:
% 0.21/0.45         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 0.21/0.45          | ~ (r1_tarski @ X15 @ X16))),
% 0.21/0.45      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf(t1_zfmisc_1, axiom,
% 0.21/0.45    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.45  thf('9', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i]: (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X17 : $i, X19 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.45  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
