%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mU0SHrKPED

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  167 ( 213 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t29_relset_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X10 )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mU0SHrKPED
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 13 iterations in 0.011s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.45  thf(t29_relset_1, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( m1_subset_1 @
% 0.21/0.45       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( m1_subset_1 @
% 0.21/0.45          ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t29_relset_1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(dt_k2_subset_1, axiom,
% 0.21/0.45    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.45  thf('2', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.45  thf('3', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X2 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t71_relat_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.45  thf('6', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.45  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t11_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ C ) =>
% 0.21/0.45       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.45           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.45         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.21/0.45          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ X10)
% 0.21/0.45          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.45          | ~ (v1_relat_1 @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X0)
% 0.21/0.45          | (m1_subset_1 @ X0 @ 
% 0.21/0.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.45          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.45          | (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.21/0.45             (k1_zfmisc_1 @ 
% 0.21/0.45              (k2_zfmisc_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X1)))
% 0.21/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.45  thf('11', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.45  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.45  thf('12', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.45          | (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.21/0.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.21/0.45      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '13'])).
% 0.21/0.45  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
