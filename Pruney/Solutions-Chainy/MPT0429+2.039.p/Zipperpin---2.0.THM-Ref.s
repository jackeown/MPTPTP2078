%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NOTgGNlGuw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 134 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X34 ) @ X35 )
      | ( r2_hidden @ ( sk_C @ X35 @ X34 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X29 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('4',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X32 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('10',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NOTgGNlGuw
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 38 iterations in 0.021s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t61_setfam_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( m1_subset_1 @
% 0.21/0.49       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( m1_subset_1 @
% 0.21/0.49          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t94_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.21/0.49       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X34 : $i, X35 : $i]:
% 0.21/0.49         ((r1_tarski @ (k3_tarski @ X34) @ X35)
% 0.21/0.49          | (r2_hidden @ (sk_C @ X35 @ X34) @ X34))),
% 0.21/0.49      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.49  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.49  thf(t55_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X29 @ X30) @ X31)
% 0.21/0.49          | ~ (r2_hidden @ X29 @ X31))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.49  thf('4', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.49  thf('6', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.49  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t79_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X32 : $i, X33 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X32) @ (k1_zfmisc_1 @ X33))
% 0.21/0.49          | ~ (r1_tarski @ X32 @ X33))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(t1_zfmisc_1, axiom,
% 0.21/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.49  thf('10', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X36 : $i, X38 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
