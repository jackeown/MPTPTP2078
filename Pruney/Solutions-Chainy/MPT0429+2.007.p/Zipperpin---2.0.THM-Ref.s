%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.omZOxw9sxl

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  90 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  145 ( 503 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( m1_subset_1 @ ( k1_tarski @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('7',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('11',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('12',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('16',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    m1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['7','16','17','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.omZOxw9sxl
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 28 iterations in 0.016s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(t61_setfam_1, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( m1_subset_1 @
% 0.21/0.44       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( m1_subset_1 @
% 0.21/0.44          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.44          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t4_subset_1, axiom,
% 0.21/0.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.44  thf(t55_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.44       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.44         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X36 : $i, X37 : $i]:
% 0.21/0.44         (((X36) = (k1_xboole_0))
% 0.21/0.44          | ~ (m1_subset_1 @ X37 @ X36)
% 0.21/0.44          | (m1_subset_1 @ (k1_tarski @ X37) @ (k1_zfmisc_1 @ X36)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.44           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.21/0.44          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('5', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t1_zfmisc_1, axiom,
% 0.21/0.45    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.45  thf('6', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.21/0.45  thf('8', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('9', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t99_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.45  thf('10', plain, (![X26 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X26)) = (X26))),
% 0.21/0.45      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.45  thf('11', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.21/0.45      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.45  thf('12', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.45  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('14', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.45  thf('15', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.45  thf('16', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('18', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.21/0.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.45  thf('20', plain, ((m1_subset_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('21', plain, ($false),
% 0.21/0.45      inference('demod', [status(thm)], ['7', '16', '17', '20'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
