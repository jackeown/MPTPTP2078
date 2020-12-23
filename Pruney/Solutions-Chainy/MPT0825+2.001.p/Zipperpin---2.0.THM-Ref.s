%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a8cXDEN5bK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  166 ( 191 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t28_relset_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X11 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a8cXDEN5bK
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:18:04 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 15 iterations in 0.013s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.49  thf(t28_relset_1, conjecture,
% 0.23/0.49    (![A:$i]: ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]: ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t28_relset_1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (~ (r1_tarski @ (k6_relat_1 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(d10_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.49  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.49  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.49  thf(t71_relat_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.49  thf('4', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.49  thf(t11_relset_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( v1_relat_1 @ C ) =>
% 0.23/0.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.23/0.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.23/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.23/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ X11)
% 0.23/0.49          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.23/0.49          | ~ (v1_relat_1 @ X9))),
% 0.23/0.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.49          | (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.23/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.23/0.49          | ~ (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X2))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.23/0.49  thf('7', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.49  thf('8', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.23/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.49          | (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.23/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.23/0.49          | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.49          | (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.23/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '9'])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.23/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '10'])).
% 0.23/0.49  thf(t3_subset, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X3 : $i, X4 : $i]:
% 0.23/0.49         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.49  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
