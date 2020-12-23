%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MIdHowUzqo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:48 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  324 ( 500 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X21: $i] :
      ( ( ( k3_relat_1 @ X21 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X21 ) @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MIdHowUzqo
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.84/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.08  % Solved by: fo/fo7.sh
% 0.84/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.08  % done 802 iterations in 0.612s
% 0.84/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.08  % SZS output start Refutation
% 0.84/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.84/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.08  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.84/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.84/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.08  thf(t19_relset_1, conjecture,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.08       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.84/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.08        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.08          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.84/1.08    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.84/1.08  thf('0', plain,
% 0.84/1.08      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(d6_relat_1, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( v1_relat_1 @ A ) =>
% 0.84/1.08       ( ( k3_relat_1 @ A ) =
% 0.84/1.08         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.84/1.08  thf('1', plain,
% 0.84/1.08      (![X21 : $i]:
% 0.84/1.08         (((k3_relat_1 @ X21)
% 0.84/1.08            = (k2_xboole_0 @ (k1_relat_1 @ X21) @ (k2_relat_1 @ X21)))
% 0.84/1.08          | ~ (v1_relat_1 @ X21))),
% 0.84/1.08      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.84/1.08  thf('2', plain,
% 0.84/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(cc2_relset_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.84/1.08  thf('3', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.84/1.08         ((v5_relat_1 @ X25 @ X27)
% 0.84/1.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.08  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.84/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.08  thf(d19_relat_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( v1_relat_1 @ B ) =>
% 0.84/1.08       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.08  thf('5', plain,
% 0.84/1.08      (![X19 : $i, X20 : $i]:
% 0.84/1.08         (~ (v5_relat_1 @ X19 @ X20)
% 0.84/1.08          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.84/1.08          | ~ (v1_relat_1 @ X19))),
% 0.84/1.08      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.84/1.08  thf('6', plain,
% 0.84/1.08      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.08  thf('7', plain,
% 0.84/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(cc1_relset_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.08       ( v1_relat_1 @ C ) ))).
% 0.84/1.08  thf('8', plain,
% 0.84/1.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.08         ((v1_relat_1 @ X22)
% 0.84/1.08          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.84/1.08  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.08  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.84/1.08      inference('demod', [status(thm)], ['6', '9'])).
% 0.84/1.08  thf(t10_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.84/1.08  thf('11', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.84/1.08      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.84/1.08  thf('12', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.08  thf('13', plain,
% 0.84/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('14', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.84/1.08         ((v4_relat_1 @ X25 @ X26)
% 0.84/1.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.08  thf('15', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.84/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.84/1.08  thf(d18_relat_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( v1_relat_1 @ B ) =>
% 0.84/1.08       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.08  thf('16', plain,
% 0.84/1.08      (![X17 : $i, X18 : $i]:
% 0.84/1.08         (~ (v4_relat_1 @ X17 @ X18)
% 0.84/1.08          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.84/1.08          | ~ (v1_relat_1 @ X17))),
% 0.84/1.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.84/1.08  thf('17', plain,
% 0.84/1.08      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.08  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.08  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.84/1.08      inference('demod', [status(thm)], ['17', '18'])).
% 0.84/1.08  thf(t12_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.84/1.08  thf('20', plain,
% 0.84/1.08      (![X6 : $i, X7 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.84/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.08  thf('21', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.08  thf(t7_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.08  thf('22', plain,
% 0.84/1.08      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.84/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.08  thf(t11_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.84/1.08  thf('23', plain,
% 0.84/1.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.08         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.84/1.08  thf('24', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.84/1.08  thf('25', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.84/1.08      inference('sup+', [status(thm)], ['21', '24'])).
% 0.84/1.08  thf(t8_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.84/1.08       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.84/1.08  thf('26', plain,
% 0.84/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.84/1.08         (~ (r1_tarski @ X10 @ X11)
% 0.84/1.08          | ~ (r1_tarski @ X12 @ X11)
% 0.84/1.08          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.84/1.08      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.84/1.08  thf('27', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.84/1.08           (k2_xboole_0 @ sk_A @ X0))
% 0.84/1.08          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['25', '26'])).
% 0.84/1.08  thf('28', plain,
% 0.84/1.08      ((r1_tarski @ 
% 0.84/1.08        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.84/1.08        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['12', '27'])).
% 0.84/1.08  thf('29', plain,
% 0.84/1.08      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.84/1.08        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.08      inference('sup+', [status(thm)], ['1', '28'])).
% 0.84/1.08  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.08  thf('31', plain,
% 0.84/1.08      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.84/1.08      inference('demod', [status(thm)], ['29', '30'])).
% 0.84/1.08  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.84/1.08  
% 0.84/1.08  % SZS output end Refutation
% 0.84/1.08  
% 0.93/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
