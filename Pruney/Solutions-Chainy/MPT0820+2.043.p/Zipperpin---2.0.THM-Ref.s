%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fDVWE8tIAH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:53 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   64 (  80 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  372 ( 528 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','23'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('33',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fDVWE8tIAH
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.33/1.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.33/1.53  % Solved by: fo/fo7.sh
% 1.33/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.53  % done 1449 iterations in 1.074s
% 1.33/1.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.33/1.53  % SZS output start Refutation
% 1.33/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.33/1.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.33/1.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.33/1.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.33/1.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.33/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.33/1.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.33/1.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.33/1.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.33/1.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.33/1.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.33/1.53  thf(sk_C_type, type, sk_C: $i).
% 1.33/1.53  thf(t19_relset_1, conjecture,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.53       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.33/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.53    (~( ![A:$i,B:$i,C:$i]:
% 1.33/1.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.53          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.33/1.53    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.33/1.53  thf('0', plain,
% 1.33/1.53      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.53  thf(d6_relat_1, axiom,
% 1.33/1.53    (![A:$i]:
% 1.33/1.53     ( ( v1_relat_1 @ A ) =>
% 1.33/1.53       ( ( k3_relat_1 @ A ) =
% 1.33/1.53         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.33/1.53  thf('1', plain,
% 1.33/1.53      (![X20 : $i]:
% 1.33/1.53         (((k3_relat_1 @ X20)
% 1.33/1.53            = (k2_xboole_0 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 1.33/1.53          | ~ (v1_relat_1 @ X20))),
% 1.33/1.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.33/1.53  thf('2', plain,
% 1.33/1.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.33/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.53  thf(dt_k2_relset_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.33/1.53  thf('3', plain,
% 1.33/1.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.33/1.53         ((m1_subset_1 @ (k2_relset_1 @ X26 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 1.33/1.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.33/1.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.33/1.53  thf('4', plain,
% 1.33/1.53      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 1.33/1.53      inference('sup-', [status(thm)], ['2', '3'])).
% 1.33/1.53  thf(t3_subset, axiom,
% 1.33/1.53    (![A:$i,B:$i]:
% 1.33/1.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.33/1.53  thf('5', plain,
% 1.33/1.53      (![X13 : $i, X14 : $i]:
% 1.33/1.53         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.33/1.53      inference('cnf', [status(esa)], [t3_subset])).
% 1.33/1.53  thf('6', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 1.33/1.53      inference('sup-', [status(thm)], ['4', '5'])).
% 1.33/1.53  thf('7', plain,
% 1.33/1.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.33/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.53  thf(redefinition_k2_relset_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.33/1.53  thf('8', plain,
% 1.33/1.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.33/1.53         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.33/1.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.33/1.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.33/1.53  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.33/1.53      inference('sup-', [status(thm)], ['7', '8'])).
% 1.33/1.53  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.33/1.53      inference('demod', [status(thm)], ['6', '9'])).
% 1.33/1.53  thf(t10_xboole_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.33/1.53  thf('11', plain,
% 1.33/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.33/1.53         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.33/1.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.33/1.53  thf('12', plain,
% 1.33/1.53      (![X0 : $i]:
% 1.33/1.53         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.33/1.53      inference('sup-', [status(thm)], ['10', '11'])).
% 1.33/1.53  thf(t7_xboole_1, axiom,
% 1.33/1.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.33/1.53  thf('13', plain,
% 1.33/1.53      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.33/1.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.33/1.53  thf('14', plain,
% 1.33/1.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.33/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.53  thf(cc2_relset_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.33/1.53  thf('15', plain,
% 1.33/1.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.33/1.53         ((v4_relat_1 @ X23 @ X24)
% 1.33/1.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.33/1.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.33/1.53  thf('16', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.33/1.53      inference('sup-', [status(thm)], ['14', '15'])).
% 1.33/1.53  thf(d18_relat_1, axiom,
% 1.33/1.53    (![A:$i,B:$i]:
% 1.33/1.53     ( ( v1_relat_1 @ B ) =>
% 1.33/1.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.33/1.53  thf('17', plain,
% 1.33/1.53      (![X18 : $i, X19 : $i]:
% 1.33/1.53         (~ (v4_relat_1 @ X18 @ X19)
% 1.33/1.53          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.33/1.53          | ~ (v1_relat_1 @ X18))),
% 1.33/1.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.33/1.53  thf('18', plain,
% 1.33/1.53      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.33/1.53      inference('sup-', [status(thm)], ['16', '17'])).
% 1.33/1.53  thf('19', plain,
% 1.33/1.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.33/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.53  thf(cc2_relat_1, axiom,
% 1.33/1.53    (![A:$i]:
% 1.33/1.53     ( ( v1_relat_1 @ A ) =>
% 1.33/1.53       ( ![B:$i]:
% 1.33/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.33/1.53  thf('20', plain,
% 1.33/1.53      (![X16 : $i, X17 : $i]:
% 1.33/1.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.33/1.53          | (v1_relat_1 @ X16)
% 1.33/1.53          | ~ (v1_relat_1 @ X17))),
% 1.33/1.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.33/1.53  thf('21', plain,
% 1.33/1.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.33/1.53      inference('sup-', [status(thm)], ['19', '20'])).
% 1.33/1.53  thf(fc6_relat_1, axiom,
% 1.33/1.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.33/1.53  thf('22', plain,
% 1.33/1.53      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.33/1.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.33/1.53  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.53      inference('demod', [status(thm)], ['21', '22'])).
% 1.33/1.53  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.33/1.53      inference('demod', [status(thm)], ['18', '23'])).
% 1.33/1.53  thf(t1_xboole_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.33/1.53       ( r1_tarski @ A @ C ) ))).
% 1.33/1.53  thf('25', plain,
% 1.33/1.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.33/1.53         (~ (r1_tarski @ X3 @ X4)
% 1.33/1.53          | ~ (r1_tarski @ X4 @ X5)
% 1.33/1.53          | (r1_tarski @ X3 @ X5))),
% 1.33/1.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.33/1.53  thf('26', plain,
% 1.33/1.53      (![X0 : $i]:
% 1.33/1.53         ((r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 1.33/1.53      inference('sup-', [status(thm)], ['24', '25'])).
% 1.33/1.53  thf('27', plain,
% 1.33/1.53      (![X0 : $i]:
% 1.33/1.53         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.33/1.53      inference('sup-', [status(thm)], ['13', '26'])).
% 1.33/1.53  thf(t8_xboole_1, axiom,
% 1.33/1.53    (![A:$i,B:$i,C:$i]:
% 1.33/1.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.33/1.53       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.33/1.53  thf('28', plain,
% 1.33/1.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.33/1.53         (~ (r1_tarski @ X8 @ X9)
% 1.33/1.53          | ~ (r1_tarski @ X10 @ X9)
% 1.33/1.53          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.33/1.53      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.33/1.53  thf('29', plain,
% 1.33/1.53      (![X0 : $i, X1 : $i]:
% 1.33/1.53         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.33/1.53           (k2_xboole_0 @ sk_A @ X0))
% 1.33/1.53          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.33/1.53      inference('sup-', [status(thm)], ['27', '28'])).
% 1.33/1.53  thf('30', plain,
% 1.33/1.53      ((r1_tarski @ 
% 1.33/1.53        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.33/1.53        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.53      inference('sup-', [status(thm)], ['12', '29'])).
% 1.33/1.53  thf('31', plain,
% 1.33/1.53      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.33/1.53        | ~ (v1_relat_1 @ sk_C))),
% 1.33/1.53      inference('sup+', [status(thm)], ['1', '30'])).
% 1.33/1.53  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.53      inference('demod', [status(thm)], ['21', '22'])).
% 1.33/1.53  thf('33', plain,
% 1.33/1.53      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.53      inference('demod', [status(thm)], ['31', '32'])).
% 1.33/1.53  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 1.33/1.53  
% 1.33/1.53  % SZS output end Refutation
% 1.33/1.53  
% 1.37/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
