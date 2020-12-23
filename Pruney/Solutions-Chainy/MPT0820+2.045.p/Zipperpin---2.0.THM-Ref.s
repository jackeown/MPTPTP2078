%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMz4gCdaGu

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:54 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   70 (  89 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  427 ( 607 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
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

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X28 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('36',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMz4gCdaGu
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.37/2.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.37/2.55  % Solved by: fo/fo7.sh
% 2.37/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.37/2.55  % done 1564 iterations in 2.090s
% 2.37/2.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.37/2.55  % SZS output start Refutation
% 2.37/2.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.37/2.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.37/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.37/2.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.37/2.55  thf(sk_C_type, type, sk_C: $i).
% 2.37/2.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.37/2.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.37/2.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.37/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.37/2.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.37/2.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.37/2.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.37/2.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.37/2.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.37/2.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.37/2.55  thf(t19_relset_1, conjecture,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.37/2.55       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.37/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.37/2.55    (~( ![A:$i,B:$i,C:$i]:
% 2.37/2.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.37/2.55          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.37/2.55    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 2.37/2.55  thf('0', plain,
% 2.37/2.55      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf(t7_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.37/2.55  thf('1', plain,
% 2.37/2.55      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 2.37/2.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.37/2.55  thf('2', plain,
% 2.37/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf(cc2_relset_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.37/2.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.37/2.55  thf('3', plain,
% 2.37/2.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.37/2.55         ((v5_relat_1 @ X25 @ X27)
% 2.37/2.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.37/2.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.37/2.55  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 2.37/2.55      inference('sup-', [status(thm)], ['2', '3'])).
% 2.37/2.55  thf(d19_relat_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( v1_relat_1 @ B ) =>
% 2.37/2.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.37/2.55  thf('5', plain,
% 2.37/2.55      (![X20 : $i, X21 : $i]:
% 2.37/2.55         (~ (v5_relat_1 @ X20 @ X21)
% 2.37/2.55          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 2.37/2.55          | ~ (v1_relat_1 @ X20))),
% 2.37/2.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.37/2.55  thf('6', plain,
% 2.37/2.55      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 2.37/2.55      inference('sup-', [status(thm)], ['4', '5'])).
% 2.37/2.55  thf('7', plain,
% 2.37/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf(cc2_relat_1, axiom,
% 2.37/2.55    (![A:$i]:
% 2.37/2.55     ( ( v1_relat_1 @ A ) =>
% 2.37/2.55       ( ![B:$i]:
% 2.37/2.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.37/2.55  thf('8', plain,
% 2.37/2.55      (![X18 : $i, X19 : $i]:
% 2.37/2.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.37/2.55          | (v1_relat_1 @ X18)
% 2.37/2.55          | ~ (v1_relat_1 @ X19))),
% 2.37/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.37/2.55  thf('9', plain,
% 2.37/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.37/2.55      inference('sup-', [status(thm)], ['7', '8'])).
% 2.37/2.55  thf(fc6_relat_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.37/2.55  thf('10', plain,
% 2.37/2.55      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 2.37/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.37/2.55  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 2.37/2.55      inference('demod', [status(thm)], ['9', '10'])).
% 2.37/2.55  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 2.37/2.55      inference('demod', [status(thm)], ['6', '11'])).
% 2.37/2.55  thf(t10_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.37/2.55  thf('13', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.37/2.55      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.55  thf('14', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 2.37/2.55      inference('sup-', [status(thm)], ['12', '13'])).
% 2.37/2.55  thf(t8_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.37/2.55       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.37/2.55  thf('15', plain,
% 2.37/2.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.55         (~ (r1_tarski @ X8 @ X9)
% 2.37/2.55          | ~ (r1_tarski @ X10 @ X9)
% 2.37/2.55          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 2.37/2.55      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.37/2.55  thf('16', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X1) @ 
% 2.37/2.55           (k2_xboole_0 @ X0 @ sk_B))
% 2.37/2.55          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['14', '15'])).
% 2.37/2.55  thf('17', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 2.37/2.55          (k2_xboole_0 @ X0 @ sk_B))),
% 2.37/2.55      inference('sup-', [status(thm)], ['1', '16'])).
% 2.37/2.55  thf(d6_relat_1, axiom,
% 2.37/2.55    (![A:$i]:
% 2.37/2.55     ( ( v1_relat_1 @ A ) =>
% 2.37/2.55       ( ( k3_relat_1 @ A ) =
% 2.37/2.55         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.37/2.55  thf('18', plain,
% 2.37/2.55      (![X22 : $i]:
% 2.37/2.55         (((k3_relat_1 @ X22)
% 2.37/2.55            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 2.37/2.55          | ~ (v1_relat_1 @ X22))),
% 2.37/2.55      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.37/2.55  thf('19', plain,
% 2.37/2.55      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 2.37/2.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.37/2.55  thf('20', plain,
% 2.37/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf(dt_k1_relset_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.37/2.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.37/2.55  thf('21', plain,
% 2.37/2.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.37/2.55         ((m1_subset_1 @ (k1_relset_1 @ X28 @ X29 @ X30) @ (k1_zfmisc_1 @ X28))
% 2.37/2.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 2.37/2.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 2.37/2.55  thf('22', plain,
% 2.37/2.55      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 2.37/2.55      inference('sup-', [status(thm)], ['20', '21'])).
% 2.37/2.55  thf(t3_subset, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.37/2.55  thf('23', plain,
% 2.37/2.55      (![X15 : $i, X16 : $i]:
% 2.37/2.55         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.37/2.55      inference('cnf', [status(esa)], [t3_subset])).
% 2.37/2.55  thf('24', plain, ((r1_tarski @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 2.37/2.55      inference('sup-', [status(thm)], ['22', '23'])).
% 2.37/2.55  thf('25', plain,
% 2.37/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf(redefinition_k1_relset_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.37/2.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.37/2.55  thf('26', plain,
% 2.37/2.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.37/2.55         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.37/2.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.37/2.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.37/2.55  thf('27', plain,
% 2.37/2.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.37/2.55      inference('sup-', [status(thm)], ['25', '26'])).
% 2.37/2.55  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.37/2.55      inference('demod', [status(thm)], ['24', '27'])).
% 2.37/2.55  thf('29', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.37/2.55      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.55  thf('30', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 2.37/2.55      inference('sup-', [status(thm)], ['28', '29'])).
% 2.37/2.55  thf('31', plain,
% 2.37/2.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.55         (~ (r1_tarski @ X8 @ X9)
% 2.37/2.55          | ~ (r1_tarski @ X10 @ X9)
% 2.37/2.55          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 2.37/2.55      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.37/2.55  thf('32', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 2.37/2.55           (k2_xboole_0 @ X0 @ sk_A))
% 2.37/2.55          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['30', '31'])).
% 2.37/2.55  thf('33', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ 
% 2.37/2.55          (k2_xboole_0 @ X0 @ sk_A))),
% 2.37/2.55      inference('sup-', [status(thm)], ['19', '32'])).
% 2.37/2.55  thf('34', plain,
% 2.37/2.55      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 2.37/2.55         (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))
% 2.37/2.55        | ~ (v1_relat_1 @ sk_C))),
% 2.37/2.55      inference('sup+', [status(thm)], ['18', '33'])).
% 2.37/2.55  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 2.37/2.55      inference('demod', [status(thm)], ['9', '10'])).
% 2.37/2.55  thf('36', plain,
% 2.37/2.55      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 2.37/2.55        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 2.37/2.55      inference('demod', [status(thm)], ['34', '35'])).
% 2.37/2.55  thf(t1_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.37/2.55       ( r1_tarski @ A @ C ) ))).
% 2.37/2.55  thf('37', plain,
% 2.37/2.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.37/2.55         (~ (r1_tarski @ X3 @ X4)
% 2.37/2.55          | ~ (r1_tarski @ X4 @ X5)
% 2.37/2.55          | (r1_tarski @ X3 @ X5))),
% 2.37/2.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.37/2.55  thf('38', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         ((r1_tarski @ (k3_relat_1 @ sk_C) @ X0)
% 2.37/2.55          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) @ X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['36', '37'])).
% 2.37/2.55  thf('39', plain,
% 2.37/2.55      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.37/2.55      inference('sup-', [status(thm)], ['17', '38'])).
% 2.37/2.55  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 2.37/2.55  
% 2.37/2.55  % SZS output end Refutation
% 2.37/2.55  
% 2.37/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
