%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rwPqrSACO

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:54 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rwPqrSACO
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.75/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.95  % Solved by: fo/fo7.sh
% 1.75/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.95  % done 1883 iterations in 1.465s
% 1.75/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.95  % SZS output start Refutation
% 1.75/1.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.75/1.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.75/1.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.75/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.95  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.75/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.75/1.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.75/1.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.75/1.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.75/1.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.75/1.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.75/1.95  thf(t19_relset_1, conjecture,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.95       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.75/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.95    (~( ![A:$i,B:$i,C:$i]:
% 1.75/1.95        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.95          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.75/1.95    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.75/1.95  thf('0', plain,
% 1.75/1.95      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(t7_xboole_1, axiom,
% 1.75/1.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.75/1.95  thf('1', plain,
% 1.75/1.95      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.75/1.95  thf('2', plain,
% 1.75/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(cc2_relset_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.75/1.95  thf('3', plain,
% 1.75/1.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.75/1.95         ((v5_relat_1 @ X25 @ X27)
% 1.75/1.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.75/1.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.75/1.95  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.75/1.95      inference('sup-', [status(thm)], ['2', '3'])).
% 1.75/1.95  thf(d19_relat_1, axiom,
% 1.75/1.95    (![A:$i,B:$i]:
% 1.75/1.95     ( ( v1_relat_1 @ B ) =>
% 1.75/1.95       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.75/1.95  thf('5', plain,
% 1.75/1.95      (![X20 : $i, X21 : $i]:
% 1.75/1.95         (~ (v5_relat_1 @ X20 @ X21)
% 1.75/1.95          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 1.75/1.95          | ~ (v1_relat_1 @ X20))),
% 1.75/1.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.75/1.95  thf('6', plain,
% 1.75/1.95      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.75/1.95      inference('sup-', [status(thm)], ['4', '5'])).
% 1.75/1.95  thf('7', plain,
% 1.75/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(cc2_relat_1, axiom,
% 1.75/1.95    (![A:$i]:
% 1.75/1.95     ( ( v1_relat_1 @ A ) =>
% 1.75/1.95       ( ![B:$i]:
% 1.75/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.75/1.95  thf('8', plain,
% 1.75/1.95      (![X18 : $i, X19 : $i]:
% 1.75/1.95         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.75/1.95          | (v1_relat_1 @ X18)
% 1.75/1.95          | ~ (v1_relat_1 @ X19))),
% 1.75/1.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.75/1.95  thf('9', plain,
% 1.75/1.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.75/1.95      inference('sup-', [status(thm)], ['7', '8'])).
% 1.75/1.95  thf(fc6_relat_1, axiom,
% 1.75/1.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.75/1.95  thf('10', plain,
% 1.75/1.95      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 1.75/1.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.75/1.95  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.95      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.95  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.75/1.95      inference('demod', [status(thm)], ['6', '11'])).
% 1.75/1.95  thf(t10_xboole_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.75/1.95  thf('13', plain,
% 1.75/1.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.75/1.95  thf('14', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.75/1.95      inference('sup-', [status(thm)], ['12', '13'])).
% 1.75/1.95  thf(t8_xboole_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.75/1.95       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.75/1.95  thf('15', plain,
% 1.75/1.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.75/1.95         (~ (r1_tarski @ X10 @ X11)
% 1.75/1.95          | ~ (r1_tarski @ X12 @ X11)
% 1.75/1.95          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 1.75/1.95      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.75/1.95  thf('16', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i]:
% 1.75/1.95         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X1) @ 
% 1.75/1.95           (k2_xboole_0 @ X0 @ sk_B))
% 1.75/1.95          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 1.75/1.95      inference('sup-', [status(thm)], ['14', '15'])).
% 1.75/1.95  thf('17', plain,
% 1.75/1.95      (![X0 : $i]:
% 1.75/1.95         (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 1.75/1.95          (k2_xboole_0 @ X0 @ sk_B))),
% 1.75/1.95      inference('sup-', [status(thm)], ['1', '16'])).
% 1.75/1.95  thf(d6_relat_1, axiom,
% 1.75/1.95    (![A:$i]:
% 1.75/1.95     ( ( v1_relat_1 @ A ) =>
% 1.75/1.95       ( ( k3_relat_1 @ A ) =
% 1.75/1.95         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.75/1.95  thf('18', plain,
% 1.75/1.95      (![X22 : $i]:
% 1.75/1.95         (((k3_relat_1 @ X22)
% 1.75/1.95            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 1.75/1.95          | ~ (v1_relat_1 @ X22))),
% 1.75/1.95      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.75/1.95  thf('19', plain,
% 1.75/1.95      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.75/1.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.75/1.95  thf('20', plain,
% 1.75/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(dt_k1_relset_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.96       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.75/1.96  thf('21', plain,
% 1.75/1.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.75/1.96         ((m1_subset_1 @ (k1_relset_1 @ X28 @ X29 @ X30) @ (k1_zfmisc_1 @ X28))
% 1.75/1.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.75/1.96      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 1.75/1.96  thf('22', plain,
% 1.75/1.96      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.75/1.96      inference('sup-', [status(thm)], ['20', '21'])).
% 1.75/1.96  thf(t3_subset, axiom,
% 1.75/1.96    (![A:$i,B:$i]:
% 1.75/1.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.75/1.96  thf('23', plain,
% 1.75/1.96      (![X15 : $i, X16 : $i]:
% 1.75/1.96         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_subset])).
% 1.75/1.96  thf('24', plain, ((r1_tarski @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 1.75/1.96      inference('sup-', [status(thm)], ['22', '23'])).
% 1.75/1.96  thf('25', plain,
% 1.75/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.96  thf(redefinition_k1_relset_1, axiom,
% 1.75/1.96    (![A:$i,B:$i,C:$i]:
% 1.75/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.75/1.96  thf('26', plain,
% 1.75/1.96      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.75/1.96         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 1.75/1.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.75/1.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.75/1.96  thf('27', plain,
% 1.75/1.96      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.75/1.96      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.96  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.75/1.96      inference('demod', [status(thm)], ['24', '27'])).
% 1.75/1.96  thf('29', plain,
% 1.75/1.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.96         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.75/1.96      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.75/1.96  thf('30', plain,
% 1.75/1.96      (![X0 : $i]:
% 1.75/1.96         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 1.75/1.96      inference('sup-', [status(thm)], ['28', '29'])).
% 1.75/1.96  thf('31', plain,
% 1.75/1.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.75/1.96         (~ (r1_tarski @ X10 @ X11)
% 1.75/1.96          | ~ (r1_tarski @ X12 @ X11)
% 1.75/1.96          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 1.75/1.96      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.75/1.96  thf('32', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.75/1.96           (k2_xboole_0 @ X0 @ sk_A))
% 1.75/1.96          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['30', '31'])).
% 1.75/1.96  thf('33', plain,
% 1.75/1.96      (![X0 : $i]:
% 1.75/1.96         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ 
% 1.75/1.96          (k2_xboole_0 @ X0 @ sk_A))),
% 1.75/1.96      inference('sup-', [status(thm)], ['19', '32'])).
% 1.75/1.96  thf('34', plain,
% 1.75/1.96      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 1.75/1.96         (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))
% 1.75/1.96        | ~ (v1_relat_1 @ sk_C))),
% 1.75/1.96      inference('sup+', [status(thm)], ['18', '33'])).
% 1.75/1.96  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.96      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.96  thf('36', plain,
% 1.75/1.96      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 1.75/1.96        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 1.75/1.96      inference('demod', [status(thm)], ['34', '35'])).
% 1.75/1.96  thf(t1_xboole_1, axiom,
% 1.75/1.96    (![A:$i,B:$i,C:$i]:
% 1.75/1.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.75/1.96       ( r1_tarski @ A @ C ) ))).
% 1.75/1.96  thf('37', plain,
% 1.75/1.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.75/1.96         (~ (r1_tarski @ X5 @ X6)
% 1.75/1.96          | ~ (r1_tarski @ X6 @ X7)
% 1.75/1.96          | (r1_tarski @ X5 @ X7))),
% 1.75/1.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.75/1.96  thf('38', plain,
% 1.75/1.96      (![X0 : $i]:
% 1.75/1.96         ((r1_tarski @ (k3_relat_1 @ sk_C) @ X0)
% 1.75/1.96          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) @ X0))),
% 1.75/1.96      inference('sup-', [status(thm)], ['36', '37'])).
% 1.75/1.96  thf('39', plain,
% 1.75/1.96      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.75/1.96      inference('sup-', [status(thm)], ['17', '38'])).
% 1.75/1.96  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 1.75/1.96  
% 1.75/1.96  % SZS output end Refutation
% 1.75/1.96  
% 1.75/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
