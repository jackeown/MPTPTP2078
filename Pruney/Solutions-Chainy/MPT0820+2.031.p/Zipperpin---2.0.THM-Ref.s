%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xItfCnaIMf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  357 ( 579 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('5',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['7','12'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('25',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('35',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xItfCnaIMf
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 420 iterations in 0.189s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.63  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(t19_relset_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.63        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d6_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ( k3_relat_1 @ A ) =
% 0.45/0.63         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X17 : $i]:
% 0.45/0.63         (((k3_relat_1 @ X17)
% 0.45/0.63            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.45/0.63          | ~ (v1_relat_1 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         ((v5_relat_1 @ X20 @ X22)
% 0.45/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('5', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(d19_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (v5_relat_1 @ X15 @ X16)
% 0.45/0.63          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.45/0.63          | ~ (v1_relat_1 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.45/0.63          | (v1_relat_1 @ X11)
% 0.45/0.63          | ~ (v1_relat_1 @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.64  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['7', '12'])).
% 0.45/0.64  thf(t9_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) =>
% 0.45/0.64       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X8 @ X9)
% 0.45/0.64          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 0.45/0.64          (k2_xboole_0 @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf(t11_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.64         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['2', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X20 @ X21)
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('21', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf(d18_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ B ) =>
% 0.45/0.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ X13 @ X14)
% 0.45/0.64          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.45/0.64          | ~ (v1_relat_1 @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('25', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X8 @ X9)
% 0.45/0.64          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ 
% 0.45/0.64          (k2_xboole_0 @ sk_A @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.64         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf(t8_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.45/0.64       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.64          | ~ (r1_tarski @ X7 @ X6)
% 0.45/0.64          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.45/0.64           (k2_xboole_0 @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((r1_tarski @ 
% 0.45/0.64        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.45/0.64        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '31'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['1', '32'])).
% 0.45/0.64  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
