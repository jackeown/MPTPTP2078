%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONF4Ho7lEg

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:49 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   73 (  94 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  445 ( 657 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('38',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONF4Ho7lEg
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:53:15 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 4.47/4.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.47/4.65  % Solved by: fo/fo7.sh
% 4.47/4.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.47/4.65  % done 3296 iterations in 4.158s
% 4.47/4.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.47/4.65  % SZS output start Refutation
% 4.47/4.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.47/4.65  thf(sk_A_type, type, sk_A: $i).
% 4.47/4.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.47/4.65  thf(sk_B_type, type, sk_B: $i).
% 4.47/4.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.47/4.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.47/4.65  thf(sk_C_type, type, sk_C: $i).
% 4.47/4.65  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.47/4.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.47/4.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.47/4.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.47/4.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.47/4.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.47/4.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.47/4.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.47/4.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.47/4.65  thf(t19_relset_1, conjecture,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 4.47/4.65  thf(zf_stmt_0, negated_conjecture,
% 4.47/4.65    (~( ![A:$i,B:$i,C:$i]:
% 4.47/4.65        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 4.47/4.65    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 4.47/4.65  thf('0', plain,
% 4.47/4.65      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 4.47/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.65  thf(t7_xboole_1, axiom,
% 4.47/4.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.47/4.65  thf('1', plain,
% 4.47/4.65      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 4.47/4.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.47/4.65  thf('2', plain,
% 4.47/4.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.47/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.65  thf(dt_k2_relset_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 4.47/4.65  thf('3', plain,
% 4.47/4.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.47/4.65         ((m1_subset_1 @ (k2_relset_1 @ X27 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 4.47/4.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.47/4.65      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 4.47/4.65  thf('4', plain,
% 4.47/4.65      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 4.47/4.65      inference('sup-', [status(thm)], ['2', '3'])).
% 4.47/4.65  thf(t3_subset, axiom,
% 4.47/4.65    (![A:$i,B:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.47/4.65  thf('5', plain,
% 4.47/4.65      (![X13 : $i, X14 : $i]:
% 4.47/4.65         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 4.47/4.65      inference('cnf', [status(esa)], [t3_subset])).
% 4.47/4.65  thf('6', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 4.47/4.65      inference('sup-', [status(thm)], ['4', '5'])).
% 4.47/4.65  thf('7', plain,
% 4.47/4.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.47/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.65  thf(redefinition_k2_relset_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.47/4.65  thf('8', plain,
% 4.47/4.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.47/4.65         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 4.47/4.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 4.47/4.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.47/4.65  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.47/4.65      inference('sup-', [status(thm)], ['7', '8'])).
% 4.47/4.65  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 4.47/4.65      inference('demod', [status(thm)], ['6', '9'])).
% 4.47/4.65  thf(t10_xboole_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.47/4.65  thf('11', plain,
% 4.47/4.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.65         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 4.47/4.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.47/4.65  thf('12', plain,
% 4.47/4.65      (![X0 : $i]:
% 4.47/4.65         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 4.47/4.65      inference('sup-', [status(thm)], ['10', '11'])).
% 4.47/4.65  thf(t8_xboole_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.47/4.65       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.47/4.65  thf('13', plain,
% 4.47/4.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.47/4.65         (~ (r1_tarski @ X8 @ X9)
% 4.47/4.65          | ~ (r1_tarski @ X10 @ X9)
% 4.47/4.65          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 4.47/4.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.47/4.65  thf('14', plain,
% 4.47/4.65      (![X0 : $i, X1 : $i]:
% 4.47/4.65         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X1) @ 
% 4.47/4.65           (k2_xboole_0 @ X0 @ sk_B))
% 4.47/4.65          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 4.47/4.65      inference('sup-', [status(thm)], ['12', '13'])).
% 4.47/4.65  thf('15', plain,
% 4.47/4.65      (![X0 : $i]:
% 4.47/4.65         (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 4.47/4.65          (k2_xboole_0 @ X0 @ sk_B))),
% 4.47/4.65      inference('sup-', [status(thm)], ['1', '14'])).
% 4.47/4.65  thf(d6_relat_1, axiom,
% 4.47/4.65    (![A:$i]:
% 4.47/4.65     ( ( v1_relat_1 @ A ) =>
% 4.47/4.65       ( ( k3_relat_1 @ A ) =
% 4.47/4.65         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.47/4.65  thf('16', plain,
% 4.47/4.65      (![X16 : $i]:
% 4.47/4.65         (((k3_relat_1 @ X16)
% 4.47/4.65            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 4.47/4.65          | ~ (v1_relat_1 @ X16))),
% 4.47/4.65      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.47/4.65  thf('17', plain,
% 4.47/4.65      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 4.47/4.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.47/4.65  thf('18', plain,
% 4.47/4.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.47/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.65  thf(cc2_relset_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.47/4.65  thf('19', plain,
% 4.47/4.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.47/4.65         ((v4_relat_1 @ X24 @ X25)
% 4.47/4.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.47/4.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.47/4.65  thf('20', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 4.47/4.65      inference('sup-', [status(thm)], ['18', '19'])).
% 4.47/4.65  thf(t209_relat_1, axiom,
% 4.47/4.65    (![A:$i,B:$i]:
% 4.47/4.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.47/4.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.47/4.65  thf('21', plain,
% 4.47/4.65      (![X17 : $i, X18 : $i]:
% 4.47/4.65         (((X17) = (k7_relat_1 @ X17 @ X18))
% 4.47/4.65          | ~ (v4_relat_1 @ X17 @ X18)
% 4.47/4.65          | ~ (v1_relat_1 @ X17))),
% 4.47/4.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.47/4.65  thf('22', plain,
% 4.47/4.65      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 4.47/4.65      inference('sup-', [status(thm)], ['20', '21'])).
% 4.47/4.65  thf('23', plain,
% 4.47/4.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.47/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.65  thf(cc1_relset_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.65       ( v1_relat_1 @ C ) ))).
% 4.47/4.65  thf('24', plain,
% 4.47/4.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.47/4.65         ((v1_relat_1 @ X21)
% 4.47/4.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.47/4.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.47/4.65  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 4.47/4.65      inference('sup-', [status(thm)], ['23', '24'])).
% 4.47/4.65  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 4.47/4.65      inference('demod', [status(thm)], ['22', '25'])).
% 4.47/4.65  thf(t87_relat_1, axiom,
% 4.47/4.65    (![A:$i,B:$i]:
% 4.47/4.65     ( ( v1_relat_1 @ B ) =>
% 4.47/4.65       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 4.47/4.65  thf('27', plain,
% 4.47/4.65      (![X19 : $i, X20 : $i]:
% 4.47/4.65         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X19 @ X20)) @ X20)
% 4.47/4.65          | ~ (v1_relat_1 @ X19))),
% 4.47/4.65      inference('cnf', [status(esa)], [t87_relat_1])).
% 4.47/4.65  thf('28', plain,
% 4.47/4.65      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 4.47/4.65      inference('sup+', [status(thm)], ['26', '27'])).
% 4.47/4.65  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 4.47/4.65      inference('sup-', [status(thm)], ['23', '24'])).
% 4.47/4.65  thf('30', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 4.47/4.65      inference('demod', [status(thm)], ['28', '29'])).
% 4.47/4.65  thf('31', plain,
% 4.47/4.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.65         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 4.47/4.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.47/4.65  thf('32', plain,
% 4.47/4.65      (![X0 : $i]:
% 4.47/4.65         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 4.47/4.65      inference('sup-', [status(thm)], ['30', '31'])).
% 4.47/4.65  thf('33', plain,
% 4.47/4.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.47/4.65         (~ (r1_tarski @ X8 @ X9)
% 4.47/4.65          | ~ (r1_tarski @ X10 @ X9)
% 4.47/4.65          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 4.47/4.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.47/4.65  thf('34', plain,
% 4.47/4.65      (![X0 : $i, X1 : $i]:
% 4.47/4.65         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 4.47/4.65           (k2_xboole_0 @ X0 @ sk_A))
% 4.47/4.65          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 4.47/4.65      inference('sup-', [status(thm)], ['32', '33'])).
% 4.47/4.65  thf('35', plain,
% 4.47/4.65      (![X0 : $i]:
% 4.47/4.65         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ 
% 4.47/4.65          (k2_xboole_0 @ X0 @ sk_A))),
% 4.47/4.65      inference('sup-', [status(thm)], ['17', '34'])).
% 4.47/4.65  thf('36', plain,
% 4.47/4.65      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 4.47/4.65         (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))
% 4.47/4.65        | ~ (v1_relat_1 @ sk_C))),
% 4.47/4.65      inference('sup+', [status(thm)], ['16', '35'])).
% 4.47/4.65  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 4.47/4.65      inference('sup-', [status(thm)], ['23', '24'])).
% 4.47/4.65  thf('38', plain,
% 4.47/4.65      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 4.47/4.65        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 4.47/4.65      inference('demod', [status(thm)], ['36', '37'])).
% 4.47/4.65  thf(t1_xboole_1, axiom,
% 4.47/4.65    (![A:$i,B:$i,C:$i]:
% 4.47/4.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.47/4.65       ( r1_tarski @ A @ C ) ))).
% 4.47/4.65  thf('39', plain,
% 4.47/4.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.47/4.65         (~ (r1_tarski @ X3 @ X4)
% 4.47/4.65          | ~ (r1_tarski @ X4 @ X5)
% 4.47/4.65          | (r1_tarski @ X3 @ X5))),
% 4.47/4.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.47/4.65  thf('40', plain,
% 4.47/4.65      (![X0 : $i]:
% 4.47/4.65         ((r1_tarski @ (k3_relat_1 @ sk_C) @ X0)
% 4.47/4.65          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) @ X0))),
% 4.47/4.65      inference('sup-', [status(thm)], ['38', '39'])).
% 4.47/4.65  thf('41', plain,
% 4.47/4.65      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 4.47/4.65      inference('sup-', [status(thm)], ['15', '40'])).
% 4.47/4.65  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 4.47/4.65  
% 4.47/4.65  % SZS output end Refutation
% 4.47/4.65  
% 4.47/4.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
