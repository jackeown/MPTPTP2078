%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ez1MfMBJlS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:53 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 ( 522 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('31',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ez1MfMBJlS
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.57/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.83  % Solved by: fo/fo7.sh
% 0.57/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.83  % done 519 iterations in 0.384s
% 0.57/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.83  % SZS output start Refutation
% 0.57/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.57/0.83  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.57/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.57/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.83  thf(t19_relset_1, conjecture,
% 0.57/0.83    (![A:$i,B:$i,C:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.83       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.57/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.83        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.83          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.57/0.83    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.57/0.83  thf('0', plain,
% 0.57/0.83      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf(d6_relat_1, axiom,
% 0.57/0.83    (![A:$i]:
% 0.57/0.83     ( ( v1_relat_1 @ A ) =>
% 0.57/0.83       ( ( k3_relat_1 @ A ) =
% 0.57/0.83         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.57/0.83  thf('1', plain,
% 0.57/0.83      (![X17 : $i]:
% 0.57/0.83         (((k3_relat_1 @ X17)
% 0.57/0.83            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.57/0.83          | ~ (v1_relat_1 @ X17))),
% 0.57/0.83      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.57/0.83  thf('2', plain,
% 0.57/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf(cc2_relset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i,C:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.57/0.83  thf('3', plain,
% 0.57/0.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.57/0.83         ((v5_relat_1 @ X20 @ X22)
% 0.57/0.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.57/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.57/0.83  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.57/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.83  thf(d19_relat_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( v1_relat_1 @ B ) =>
% 0.57/0.83       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.83  thf('5', plain,
% 0.57/0.83      (![X15 : $i, X16 : $i]:
% 0.57/0.83         (~ (v5_relat_1 @ X15 @ X16)
% 0.57/0.83          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.57/0.83          | ~ (v1_relat_1 @ X15))),
% 0.57/0.83      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.57/0.83  thf('6', plain,
% 0.57/0.83      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.57/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.57/0.84  thf('7', plain,
% 0.57/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.84  thf(cc2_relat_1, axiom,
% 0.57/0.84    (![A:$i]:
% 0.57/0.84     ( ( v1_relat_1 @ A ) =>
% 0.57/0.84       ( ![B:$i]:
% 0.57/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.57/0.84  thf('8', plain,
% 0.57/0.84      (![X11 : $i, X12 : $i]:
% 0.57/0.84         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.57/0.84          | (v1_relat_1 @ X11)
% 0.57/0.84          | ~ (v1_relat_1 @ X12))),
% 0.57/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.57/0.84  thf('9', plain,
% 0.57/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.57/0.84      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.84  thf(fc6_relat_1, axiom,
% 0.57/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.57/0.84  thf('10', plain,
% 0.57/0.84      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.57/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.57/0.84  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.57/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.84  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.57/0.84      inference('demod', [status(thm)], ['6', '11'])).
% 0.57/0.84  thf(t10_xboole_1, axiom,
% 0.57/0.84    (![A:$i,B:$i,C:$i]:
% 0.57/0.84     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.57/0.84  thf('13', plain,
% 0.57/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.84         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.57/0.84      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.57/0.84  thf('14', plain,
% 0.57/0.84      (![X0 : $i]:
% 0.57/0.84         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.57/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.84  thf(t7_xboole_1, axiom,
% 0.57/0.84    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.84  thf('15', plain,
% 0.57/0.84      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.57/0.84      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.84  thf('16', plain,
% 0.57/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.84  thf('17', plain,
% 0.57/0.84      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.57/0.84         ((v4_relat_1 @ X20 @ X21)
% 0.57/0.84          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.57/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.57/0.84  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.57/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.84  thf(d18_relat_1, axiom,
% 0.57/0.84    (![A:$i,B:$i]:
% 0.57/0.84     ( ( v1_relat_1 @ B ) =>
% 0.57/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.84  thf('19', plain,
% 0.57/0.84      (![X13 : $i, X14 : $i]:
% 0.57/0.84         (~ (v4_relat_1 @ X13 @ X14)
% 0.57/0.84          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.57/0.84          | ~ (v1_relat_1 @ X13))),
% 0.57/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.57/0.84  thf('20', plain,
% 0.57/0.84      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.57/0.84      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.84  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.57/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.84  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.57/0.84      inference('demod', [status(thm)], ['20', '21'])).
% 0.57/0.84  thf(t1_xboole_1, axiom,
% 0.57/0.84    (![A:$i,B:$i,C:$i]:
% 0.57/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.84       ( r1_tarski @ A @ C ) ))).
% 0.57/0.84  thf('23', plain,
% 0.57/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.84         (~ (r1_tarski @ X3 @ X4)
% 0.57/0.84          | ~ (r1_tarski @ X4 @ X5)
% 0.57/0.84          | (r1_tarski @ X3 @ X5))),
% 0.57/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.84  thf('24', plain,
% 0.57/0.84      (![X0 : $i]:
% 0.57/0.84         ((r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.57/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.84  thf('25', plain,
% 0.57/0.84      (![X0 : $i]:
% 0.57/0.84         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.57/0.84      inference('sup-', [status(thm)], ['15', '24'])).
% 0.57/0.84  thf(t8_xboole_1, axiom,
% 0.57/0.84    (![A:$i,B:$i,C:$i]:
% 0.57/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.57/0.84       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.84  thf('26', plain,
% 0.57/0.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.57/0.84         (~ (r1_tarski @ X8 @ X9)
% 0.57/0.84          | ~ (r1_tarski @ X10 @ X9)
% 0.57/0.84          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.57/0.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.57/0.84  thf('27', plain,
% 0.57/0.84      (![X0 : $i, X1 : $i]:
% 0.57/0.84         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.57/0.84           (k2_xboole_0 @ sk_A @ X0))
% 0.57/0.84          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.57/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.57/0.84  thf('28', plain,
% 0.57/0.84      ((r1_tarski @ 
% 0.57/0.84        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.57/0.84        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.84      inference('sup-', [status(thm)], ['14', '27'])).
% 0.57/0.84  thf('29', plain,
% 0.57/0.84      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.57/0.84        | ~ (v1_relat_1 @ sk_C))),
% 0.57/0.84      inference('sup+', [status(thm)], ['1', '28'])).
% 0.57/0.84  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.57/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.84  thf('31', plain,
% 0.57/0.84      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.57/0.84  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.57/0.84  
% 0.57/0.84  % SZS output end Refutation
% 0.57/0.84  
% 0.57/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
