%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uetRDyXB9F

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:55 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   70 (  94 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  404 ( 620 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X28 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('37',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uetRDyXB9F
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.10/2.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.10/2.29  % Solved by: fo/fo7.sh
% 2.10/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.10/2.29  % done 2062 iterations in 1.796s
% 2.10/2.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.10/2.29  % SZS output start Refutation
% 2.10/2.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.10/2.29  thf(sk_C_type, type, sk_C: $i).
% 2.10/2.29  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.10/2.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.10/2.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.10/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.10/2.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.10/2.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.10/2.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.10/2.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.10/2.29  thf(sk_B_type, type, sk_B: $i).
% 2.10/2.29  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.10/2.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.10/2.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.10/2.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.10/2.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.10/2.29  thf(t19_relset_1, conjecture,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.29       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.10/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.10/2.29    (~( ![A:$i,B:$i,C:$i]:
% 2.10/2.29        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.29          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.10/2.29    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 2.10/2.29  thf('0', plain,
% 2.10/2.29      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.10/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.29  thf(d6_relat_1, axiom,
% 2.10/2.29    (![A:$i]:
% 2.10/2.29     ( ( v1_relat_1 @ A ) =>
% 2.10/2.29       ( ( k3_relat_1 @ A ) =
% 2.10/2.29         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.10/2.29  thf('1', plain,
% 2.10/2.29      (![X18 : $i]:
% 2.10/2.29         (((k3_relat_1 @ X18)
% 2.10/2.29            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 2.10/2.29          | ~ (v1_relat_1 @ X18))),
% 2.10/2.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.10/2.29  thf('2', plain,
% 2.10/2.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.29  thf(dt_k2_relset_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.29       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.10/2.29  thf('3', plain,
% 2.10/2.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.10/2.29         ((m1_subset_1 @ (k2_relset_1 @ X28 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 2.10/2.29          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 2.10/2.29      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.10/2.29  thf('4', plain,
% 2.10/2.29      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 2.10/2.29      inference('sup-', [status(thm)], ['2', '3'])).
% 2.10/2.29  thf(t3_subset, axiom,
% 2.10/2.29    (![A:$i,B:$i]:
% 2.10/2.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.10/2.29  thf('5', plain,
% 2.10/2.29      (![X13 : $i, X14 : $i]:
% 2.10/2.29         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 2.10/2.29      inference('cnf', [status(esa)], [t3_subset])).
% 2.10/2.29  thf('6', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 2.10/2.29      inference('sup-', [status(thm)], ['4', '5'])).
% 2.10/2.29  thf('7', plain,
% 2.10/2.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.29  thf(redefinition_k2_relset_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.10/2.29  thf('8', plain,
% 2.10/2.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.10/2.29         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 2.10/2.29          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.10/2.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.10/2.29  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.10/2.29      inference('sup-', [status(thm)], ['7', '8'])).
% 2.10/2.29  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 2.10/2.29      inference('demod', [status(thm)], ['6', '9'])).
% 2.10/2.29  thf(t10_xboole_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.10/2.29  thf('11', plain,
% 2.10/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.10/2.29         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.10/2.29      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.10/2.29  thf('12', plain,
% 2.10/2.29      (![X0 : $i]:
% 2.10/2.29         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 2.10/2.29      inference('sup-', [status(thm)], ['10', '11'])).
% 2.10/2.29  thf(t7_xboole_1, axiom,
% 2.10/2.29    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.10/2.29  thf('13', plain,
% 2.10/2.29      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 2.10/2.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.10/2.29  thf('14', plain,
% 2.10/2.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.29  thf(cc2_relset_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.10/2.29  thf('15', plain,
% 2.10/2.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.10/2.29         ((v4_relat_1 @ X25 @ X26)
% 2.10/2.29          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.10/2.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.10/2.29  thf('16', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.10/2.29      inference('sup-', [status(thm)], ['14', '15'])).
% 2.10/2.29  thf(t209_relat_1, axiom,
% 2.10/2.29    (![A:$i,B:$i]:
% 2.10/2.29     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.10/2.29       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.10/2.29  thf('17', plain,
% 2.10/2.29      (![X21 : $i, X22 : $i]:
% 2.10/2.29         (((X21) = (k7_relat_1 @ X21 @ X22))
% 2.10/2.29          | ~ (v4_relat_1 @ X21 @ X22)
% 2.10/2.29          | ~ (v1_relat_1 @ X21))),
% 2.10/2.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.10/2.29  thf('18', plain,
% 2.10/2.29      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 2.10/2.29      inference('sup-', [status(thm)], ['16', '17'])).
% 2.10/2.29  thf('19', plain,
% 2.10/2.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.29  thf(cc2_relat_1, axiom,
% 2.10/2.29    (![A:$i]:
% 2.10/2.29     ( ( v1_relat_1 @ A ) =>
% 2.10/2.29       ( ![B:$i]:
% 2.10/2.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.10/2.29  thf('20', plain,
% 2.10/2.29      (![X16 : $i, X17 : $i]:
% 2.10/2.29         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.10/2.29          | (v1_relat_1 @ X16)
% 2.10/2.29          | ~ (v1_relat_1 @ X17))),
% 2.10/2.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.10/2.29  thf('21', plain,
% 2.10/2.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.10/2.29      inference('sup-', [status(thm)], ['19', '20'])).
% 2.10/2.29  thf(fc6_relat_1, axiom,
% 2.10/2.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.10/2.29  thf('22', plain,
% 2.10/2.29      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 2.10/2.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.10/2.29  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 2.10/2.29      inference('demod', [status(thm)], ['21', '22'])).
% 2.10/2.29  thf('24', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.10/2.29      inference('demod', [status(thm)], ['18', '23'])).
% 2.10/2.29  thf(t87_relat_1, axiom,
% 2.10/2.29    (![A:$i,B:$i]:
% 2.10/2.29     ( ( v1_relat_1 @ B ) =>
% 2.10/2.29       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.10/2.29  thf('25', plain,
% 2.10/2.29      (![X23 : $i, X24 : $i]:
% 2.10/2.29         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 2.10/2.29          | ~ (v1_relat_1 @ X23))),
% 2.10/2.29      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.10/2.29  thf('26', plain,
% 2.10/2.29      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 2.10/2.29      inference('sup+', [status(thm)], ['24', '25'])).
% 2.10/2.29  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 2.10/2.29      inference('demod', [status(thm)], ['21', '22'])).
% 2.10/2.29  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.10/2.29      inference('demod', [status(thm)], ['26', '27'])).
% 2.10/2.29  thf(t1_xboole_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.10/2.29       ( r1_tarski @ A @ C ) ))).
% 2.10/2.29  thf('29', plain,
% 2.10/2.29      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.10/2.29         (~ (r1_tarski @ X3 @ X4)
% 2.10/2.29          | ~ (r1_tarski @ X4 @ X5)
% 2.10/2.29          | (r1_tarski @ X3 @ X5))),
% 2.10/2.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.10/2.29  thf('30', plain,
% 2.10/2.29      (![X0 : $i]:
% 2.10/2.29         ((r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 2.10/2.29      inference('sup-', [status(thm)], ['28', '29'])).
% 2.10/2.29  thf('31', plain,
% 2.10/2.29      (![X0 : $i]:
% 2.10/2.29         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 2.10/2.29      inference('sup-', [status(thm)], ['13', '30'])).
% 2.10/2.29  thf(t8_xboole_1, axiom,
% 2.10/2.29    (![A:$i,B:$i,C:$i]:
% 2.10/2.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.10/2.29       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.10/2.29  thf('32', plain,
% 2.10/2.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.10/2.29         (~ (r1_tarski @ X8 @ X9)
% 2.10/2.29          | ~ (r1_tarski @ X10 @ X9)
% 2.10/2.29          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 2.10/2.29      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.10/2.29  thf('33', plain,
% 2.10/2.29      (![X0 : $i, X1 : $i]:
% 2.10/2.29         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 2.10/2.29           (k2_xboole_0 @ sk_A @ X0))
% 2.10/2.29          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.10/2.29      inference('sup-', [status(thm)], ['31', '32'])).
% 2.10/2.29  thf('34', plain,
% 2.10/2.29      ((r1_tarski @ 
% 2.10/2.29        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 2.10/2.29        (k2_xboole_0 @ sk_A @ sk_B))),
% 2.10/2.29      inference('sup-', [status(thm)], ['12', '33'])).
% 2.10/2.29  thf('35', plain,
% 2.10/2.29      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 2.10/2.29        | ~ (v1_relat_1 @ sk_C))),
% 2.10/2.29      inference('sup+', [status(thm)], ['1', '34'])).
% 2.10/2.29  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 2.10/2.29      inference('demod', [status(thm)], ['21', '22'])).
% 2.10/2.29  thf('37', plain,
% 2.10/2.29      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.10/2.29      inference('demod', [status(thm)], ['35', '36'])).
% 2.10/2.29  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 2.10/2.29  
% 2.10/2.29  % SZS output end Refutation
% 2.10/2.29  
% 2.13/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
