%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PTy4yGXAnD

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:53 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  338 ( 542 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PTy4yGXAnD
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 590 iterations in 0.469s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(t19_relset_1, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.98        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(d6_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ( k3_relat_1 @ A ) =
% 0.76/0.98         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      (![X19 : $i]:
% 0.76/0.98         (((k3_relat_1 @ X19)
% 0.76/0.98            = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.76/0.98          | ~ (v1_relat_1 @ X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.98         ((v5_relat_1 @ X22 @ X24)
% 0.76/0.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.98  thf(d19_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         (~ (v5_relat_1 @ X17 @ X18)
% 0.76/0.98          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.76/0.98          | ~ (v1_relat_1 @ X17))),
% 0.76/0.98      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X13 : $i, X14 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.76/0.98          | (v1_relat_1 @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X14))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('9', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.98  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '11'])).
% 0.76/0.98  thf(t10_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X22 @ X23)
% 0.76/0.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('17', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.98  thf(d18_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (![X15 : $i, X16 : $i]:
% 0.76/0.98         (~ (v4_relat_1 @ X15 @ X16)
% 0.76/0.98          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.76/0.98          | ~ (v1_relat_1 @ X15))),
% 0.76/0.98      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.98  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.98  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.98  thf(t12_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('23', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.98  thf(t7_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.76/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.98  thf(t11_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.98         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['23', '26'])).
% 0.76/0.98  thf(t8_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.76/0.98       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X10 @ X11)
% 0.76/0.98          | ~ (r1_tarski @ X12 @ X11)
% 0.76/0.98          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.76/0.98      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.76/0.98           (k2_xboole_0 @ sk_A @ X0))
% 0.76/0.98          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      ((r1_tarski @ 
% 0.76/0.98        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.76/0.98        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['14', '29'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.98      inference('sup+', [status(thm)], ['1', '30'])).
% 0.76/0.98  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/0.98  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
