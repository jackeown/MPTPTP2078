%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LftDA9ZIhZ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  293 ( 457 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k5_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X6 @ X7 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( r1_tarski @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['4','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LftDA9ZIhZ
% 0.17/0.36  % Computer   : n001.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 20:58:00 EST 2020
% 0.17/0.36  % CPUTime    : 
% 0.17/0.36  % Running portfolio for 600 s
% 0.17/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 22 iterations in 0.011s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.45  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.45  thf(t33_relset_1, conjecture,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.23/0.45       ( m1_subset_1 @
% 0.23/0.45         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.23/0.45         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.23/0.45          ( m1_subset_1 @
% 0.23/0.45            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.23/0.45            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.23/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(redefinition_k5_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.45       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.45         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.23/0.45          | ((k5_relset_1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 0.23/0.45      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf('4', plain,
% 0.23/0.45      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.23/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.45  thf(t87_relat_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( v1_relat_1 @ B ) =>
% 0.23/0.45       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.23/0.45  thf('5', plain,
% 0.23/0.45      (![X4 : $i, X5 : $i]:
% 0.23/0.45         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X4 @ X5)) @ X5)
% 0.23/0.45          | ~ (v1_relat_1 @ X4))),
% 0.23/0.45      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.23/0.45  thf(t88_relat_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.23/0.45  thf('6', plain,
% 0.23/0.45      (![X6 : $i, X7 : $i]:
% 0.23/0.45         ((r1_tarski @ (k7_relat_1 @ X6 @ X7) @ X6) | ~ (v1_relat_1 @ X6))),
% 0.23/0.45      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.23/0.45  thf('7', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(t4_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.23/0.45       ( ( r1_tarski @ A @ D ) =>
% 0.23/0.45         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.23/0.45  thf('8', plain,
% 0.23/0.45      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.45         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.23/0.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.23/0.45          | ~ (r1_tarski @ X16 @ X19))),
% 0.23/0.45      inference('cnf', [status(esa)], [t4_relset_1])).
% 0.23/0.45  thf('9', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (r1_tarski @ X0 @ sk_D)
% 0.23/0.45          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf('10', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (v1_relat_1 @ sk_D)
% 0.23/0.45          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.23/0.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.45  thf('11', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(cc2_relat_1, axiom,
% 0.23/0.45    (![A:$i]:
% 0.23/0.45     ( ( v1_relat_1 @ A ) =>
% 0.23/0.45       ( ![B:$i]:
% 0.23/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.45  thf('12', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.45          | (v1_relat_1 @ X0)
% 0.23/0.45          | ~ (v1_relat_1 @ X1))),
% 0.23/0.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.45  thf('13', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.23/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.45  thf(fc6_relat_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.45  thf('14', plain,
% 0.23/0.45      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.23/0.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.45  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.45  thf('16', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.23/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.45      inference('demod', [status(thm)], ['10', '15'])).
% 0.23/0.45  thf(t13_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.23/0.45       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.23/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.23/0.45  thf('17', plain,
% 0.23/0.45      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.45         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.23/0.45          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.23/0.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.23/0.45      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.23/0.45  thf('18', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.23/0.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.23/0.45          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.45  thf('19', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (v1_relat_1 @ sk_D)
% 0.23/0.45          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.23/0.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['5', '18'])).
% 0.23/0.45  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.45  thf('21', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.23/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.23/0.45      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.45  thf('22', plain, ($false), inference('demod', [status(thm)], ['4', '21'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
