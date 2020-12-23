%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXjUBkmcQB

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:48 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  304 ( 480 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','9'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('29',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXjUBkmcQB
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 555 iterations in 0.752s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.01/1.21  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.01/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.21  thf(t19_relset_1, conjecture,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i,B:$i,C:$i]:
% 1.01/1.21        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(d6_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ( k3_relat_1 @ A ) =
% 1.01/1.21         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (![X17 : $i]:
% 1.01/1.21         (((k3_relat_1 @ X17)
% 1.01/1.21            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 1.01/1.21          | ~ (v1_relat_1 @ X17))),
% 1.01/1.21      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.01/1.21  thf('2', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(cc2_relset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.21         ((v5_relat_1 @ X21 @ X23)
% 1.01/1.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.01/1.21  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.01/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(d19_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.01/1.21  thf('5', plain,
% 1.01/1.21      (![X15 : $i, X16 : $i]:
% 1.01/1.21         (~ (v5_relat_1 @ X15 @ X16)
% 1.01/1.21          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.01/1.21          | ~ (v1_relat_1 @ X15))),
% 1.01/1.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.21  thf('7', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(cc1_relset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( v1_relat_1 @ C ) ))).
% 1.01/1.21  thf('8', plain,
% 1.01/1.21      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.21         ((v1_relat_1 @ X18)
% 1.01/1.21          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.01/1.21  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.21  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.01/1.21      inference('demod', [status(thm)], ['6', '9'])).
% 1.01/1.21  thf(t10_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.01/1.21  thf('12', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 1.01/1.21  thf(t7_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('13', plain,
% 1.01/1.21      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.01/1.21      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.01/1.21  thf('14', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('15', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.21         ((v4_relat_1 @ X21 @ X22)
% 1.01/1.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.01/1.21  thf('16', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.01/1.21      inference('sup-', [status(thm)], ['14', '15'])).
% 1.01/1.21  thf(d18_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.01/1.21  thf('17', plain,
% 1.01/1.21      (![X13 : $i, X14 : $i]:
% 1.01/1.21         (~ (v4_relat_1 @ X13 @ X14)
% 1.01/1.21          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.01/1.21          | ~ (v1_relat_1 @ X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.01/1.21  thf('18', plain,
% 1.01/1.21      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['16', '17'])).
% 1.01/1.21  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.21  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.01/1.21      inference('demod', [status(thm)], ['18', '19'])).
% 1.01/1.21  thf(t1_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.01/1.21       ( r1_tarski @ A @ C ) ))).
% 1.01/1.21  thf('21', plain,
% 1.01/1.21      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X3 @ X4)
% 1.01/1.21          | ~ (r1_tarski @ X4 @ X5)
% 1.01/1.21          | (r1_tarski @ X3 @ X5))),
% 1.01/1.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.01/1.21  thf('22', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['13', '22'])).
% 1.01/1.21  thf(t8_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.01/1.21       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.01/1.21  thf('24', plain,
% 1.01/1.21      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X8 @ X9)
% 1.01/1.21          | ~ (r1_tarski @ X10 @ X9)
% 1.01/1.21          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.01/1.21      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.01/1.21           (k2_xboole_0 @ sk_A @ X0))
% 1.01/1.21          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['23', '24'])).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      ((r1_tarski @ 
% 1.01/1.21        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.01/1.21        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['12', '25'])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.01/1.21        | ~ (v1_relat_1 @ sk_C))),
% 1.01/1.21      inference('sup+', [status(thm)], ['1', '26'])).
% 1.01/1.21  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.21  thf('29', plain,
% 1.01/1.21      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['27', '28'])).
% 1.01/1.21  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 1.01/1.21  
% 1.01/1.21  % SZS output end Refutation
% 1.01/1.21  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
