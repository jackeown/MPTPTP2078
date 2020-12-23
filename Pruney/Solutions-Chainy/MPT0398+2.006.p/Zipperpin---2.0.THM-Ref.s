%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ij7CuQjNrK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(t20_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ k1_xboole_0 @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ k1_xboole_0 @ A ) ),
    inference('cnf.neg',[status(esa)],[t20_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t17_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ij7CuQjNrK
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 7 iterations in 0.009s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.46  thf(t20_setfam_1, conjecture, (![A:$i]: ( r1_setfam_1 @ k1_xboole_0 @ A ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( r1_setfam_1 @ k1_xboole_0 @ A ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t20_setfam_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_setfam_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t4_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t17_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]: ((r1_setfam_1 @ X1 @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t17_setfam_1])).
% 0.20/0.46  thf('5', plain, (![X0 : $i]: (r1_setfam_1 @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ($false), inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
