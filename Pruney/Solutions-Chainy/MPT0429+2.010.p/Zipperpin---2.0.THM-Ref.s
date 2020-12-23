%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AIuJ6sGk76

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:31 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 209 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AIuJ6sGk76
% 0.14/0.37  % Computer   : n009.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:04:26 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 36 iterations in 0.020s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(t61_setfam_1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( m1_subset_1 @
% 0.24/0.50       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( m1_subset_1 @
% 0.24/0.50          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.24/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.50  thf('1', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.24/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.50  thf(d1_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.50         (~ (r1_tarski @ X12 @ X13)
% 0.24/0.50          | (r2_hidden @ X12 @ X14)
% 0.24/0.50          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X12 : $i, X13 : $i]:
% 0.24/0.50         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.24/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.50  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.24/0.50  thf(d3_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X1 : $i, X3 : $i]:
% 0.24/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf(t1_zfmisc_1, axiom,
% 0.24/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.24/0.50  thf('6', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.24/0.50          | (r1_tarski @ X15 @ X13)
% 0.24/0.50          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X13 : $i, X15 : $i]:
% 0.24/0.50         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ (k1_tarski @ k1_xboole_0))
% 0.24/0.50          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0)
% 0.24/0.50          | (r1_tarski @ (sk_C @ X0 @ (k1_tarski @ k1_xboole_0)) @ k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '9'])).
% 0.24/0.50  thf(t3_xboole_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0)
% 0.24/0.50          | ((sk_C @ X0 @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X1 : $i, X3 : $i]:
% 0.24/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.24/0.50          | (r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0)
% 0.24/0.50          | (r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0)
% 0.24/0.50          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.24/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      (![X0 : $i]: (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '15'])).
% 0.24/0.50  thf(t3_subset, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X17 : $i, X19 : $i]:
% 0.24/0.50         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.24/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
