%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ycSSDidIde

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:51 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  416 ( 684 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('45',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.19  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.20  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ycSSDidIde
% 0.12/0.41  % Computer   : n003.cluster.edu
% 0.12/0.41  % Model      : x86_64 x86_64
% 0.12/0.41  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.41  % Memory     : 8042.1875MB
% 0.12/0.41  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.41  % CPULimit   : 60
% 0.12/0.41  % DateTime   : Tue Dec  1 16:56:12 EST 2020
% 0.12/0.41  % CPUTime    : 
% 0.12/0.41  % Running portfolio for 600 s
% 0.12/0.41  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.41  % Number of cores: 8
% 0.12/0.42  % Python version: Python 3.6.8
% 0.12/0.42  % Running in FO mode
% 1.66/1.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.94  % Solved by: fo/fo7.sh
% 1.66/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.94  % done 2471 iterations in 1.423s
% 1.66/1.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.94  % SZS output start Refutation
% 1.66/1.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.66/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.94  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.66/1.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.66/1.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.66/1.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.94  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.94  thf(t19_relset_1, conjecture,
% 1.66/1.94    (![A:$i,B:$i,C:$i]:
% 1.66/1.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.94       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.66/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.94    (~( ![A:$i,B:$i,C:$i]:
% 1.66/1.94        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.94          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.66/1.94    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.66/1.94  thf('0', plain,
% 1.66/1.94      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.66/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.94  thf(d6_relat_1, axiom,
% 1.66/1.94    (![A:$i]:
% 1.66/1.94     ( ( v1_relat_1 @ A ) =>
% 1.66/1.94       ( ( k3_relat_1 @ A ) =
% 1.66/1.94         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.66/1.94  thf('1', plain,
% 1.66/1.94      (![X20 : $i]:
% 1.66/1.94         (((k3_relat_1 @ X20)
% 1.66/1.94            = (k2_xboole_0 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 1.66/1.94          | ~ (v1_relat_1 @ X20))),
% 1.66/1.94      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.66/1.94  thf('2', plain,
% 1.66/1.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.94  thf(cc2_relset_1, axiom,
% 1.66/1.94    (![A:$i,B:$i,C:$i]:
% 1.66/1.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.66/1.94  thf('3', plain,
% 1.66/1.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.66/1.94         ((v5_relat_1 @ X23 @ X25)
% 1.66/1.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.66/1.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.94  thf('4', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.66/1.94      inference('sup-', [status(thm)], ['2', '3'])).
% 1.66/1.94  thf(d19_relat_1, axiom,
% 1.66/1.94    (![A:$i,B:$i]:
% 1.66/1.94     ( ( v1_relat_1 @ B ) =>
% 1.66/1.94       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.66/1.94  thf('5', plain,
% 1.66/1.94      (![X18 : $i, X19 : $i]:
% 1.66/1.94         (~ (v5_relat_1 @ X18 @ X19)
% 1.66/1.94          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 1.66/1.94          | ~ (v1_relat_1 @ X18))),
% 1.66/1.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.66/1.94  thf('6', plain,
% 1.66/1.94      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.66/1.94      inference('sup-', [status(thm)], ['4', '5'])).
% 1.66/1.94  thf('7', plain,
% 1.66/1.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.94  thf(cc2_relat_1, axiom,
% 1.66/1.94    (![A:$i]:
% 1.66/1.94     ( ( v1_relat_1 @ A ) =>
% 1.66/1.94       ( ![B:$i]:
% 1.66/1.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.66/1.94  thf('8', plain,
% 1.66/1.94      (![X14 : $i, X15 : $i]:
% 1.66/1.94         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.66/1.94          | (v1_relat_1 @ X14)
% 1.66/1.94          | ~ (v1_relat_1 @ X15))),
% 1.66/1.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.94  thf('9', plain,
% 1.66/1.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.66/1.94      inference('sup-', [status(thm)], ['7', '8'])).
% 1.66/1.94  thf(fc6_relat_1, axiom,
% 1.66/1.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.66/1.94  thf('10', plain,
% 1.66/1.94      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.66/1.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.66/1.94  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.94      inference('demod', [status(thm)], ['9', '10'])).
% 1.66/1.94  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.66/1.94      inference('demod', [status(thm)], ['6', '11'])).
% 1.66/1.94  thf(t12_xboole_1, axiom,
% 1.66/1.94    (![A:$i,B:$i]:
% 1.66/1.94     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.66/1.94  thf('13', plain,
% 1.66/1.94      (![X5 : $i, X6 : $i]:
% 1.66/1.94         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.66/1.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.66/1.94  thf('14', plain, (((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 1.66/1.94      inference('sup-', [status(thm)], ['12', '13'])).
% 1.66/1.94  thf(commutativity_k2_xboole_0, axiom,
% 1.66/1.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.66/1.94  thf('15', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.66/1.94  thf('16', plain, (((k2_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) = (sk_B))),
% 1.66/1.94      inference('demod', [status(thm)], ['14', '15'])).
% 1.66/1.94  thf('17', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.66/1.94  thf(t7_xboole_1, axiom,
% 1.66/1.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.66/1.94  thf('18', plain,
% 1.66/1.94      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.66/1.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.66/1.94  thf('19', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.94      inference('sup+', [status(thm)], ['17', '18'])).
% 1.66/1.94  thf('20', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.66/1.94  thf(t11_xboole_1, axiom,
% 1.66/1.94    (![A:$i,B:$i,C:$i]:
% 1.66/1.94     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.66/1.94  thf('21', plain,
% 1.66/1.94      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.94         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 1.66/1.94      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.66/1.94  thf('22', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.94         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 1.66/1.94      inference('sup-', [status(thm)], ['20', '21'])).
% 1.66/1.94  thf('23', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.94         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.94      inference('sup-', [status(thm)], ['19', '22'])).
% 1.66/1.94  thf('24', plain,
% 1.66/1.94      (![X0 : $i]:
% 1.66/1.94         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.66/1.94      inference('sup+', [status(thm)], ['16', '23'])).
% 1.66/1.94  thf('25', plain,
% 1.66/1.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.94  thf('26', plain,
% 1.66/1.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.66/1.94         ((v4_relat_1 @ X23 @ X24)
% 1.66/1.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.66/1.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.94  thf('27', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.66/1.94      inference('sup-', [status(thm)], ['25', '26'])).
% 1.66/1.94  thf(d18_relat_1, axiom,
% 1.66/1.94    (![A:$i,B:$i]:
% 1.66/1.94     ( ( v1_relat_1 @ B ) =>
% 1.66/1.94       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.66/1.94  thf('28', plain,
% 1.66/1.94      (![X16 : $i, X17 : $i]:
% 1.66/1.94         (~ (v4_relat_1 @ X16 @ X17)
% 1.66/1.94          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 1.66/1.94          | ~ (v1_relat_1 @ X16))),
% 1.66/1.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.66/1.94  thf('29', plain,
% 1.66/1.94      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.66/1.94      inference('sup-', [status(thm)], ['27', '28'])).
% 1.66/1.94  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.94      inference('demod', [status(thm)], ['9', '10'])).
% 1.66/1.94  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.66/1.94      inference('demod', [status(thm)], ['29', '30'])).
% 1.66/1.94  thf('32', plain,
% 1.66/1.94      (![X5 : $i, X6 : $i]:
% 1.66/1.94         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.66/1.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.66/1.94  thf('33', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 1.66/1.94      inference('sup-', [status(thm)], ['31', '32'])).
% 1.66/1.94  thf('34', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.66/1.94  thf('35', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 1.66/1.94      inference('demod', [status(thm)], ['33', '34'])).
% 1.66/1.94  thf('36', plain,
% 1.66/1.94      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.66/1.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.66/1.94  thf('37', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.94         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 1.66/1.94      inference('sup-', [status(thm)], ['20', '21'])).
% 1.66/1.94  thf('38', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.94         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 1.66/1.94      inference('sup-', [status(thm)], ['36', '37'])).
% 1.66/1.94  thf('39', plain,
% 1.66/1.94      (![X0 : $i]:
% 1.66/1.94         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.66/1.94      inference('sup+', [status(thm)], ['35', '38'])).
% 1.66/1.94  thf(t8_xboole_1, axiom,
% 1.66/1.94    (![A:$i,B:$i,C:$i]:
% 1.66/1.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.66/1.94       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.66/1.94  thf('40', plain,
% 1.66/1.94      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.66/1.94         (~ (r1_tarski @ X9 @ X10)
% 1.66/1.94          | ~ (r1_tarski @ X11 @ X10)
% 1.66/1.94          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 1.66/1.94      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.94  thf('41', plain,
% 1.66/1.94      (![X0 : $i, X1 : $i]:
% 1.66/1.94         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.66/1.94           (k2_xboole_0 @ sk_A @ X0))
% 1.66/1.94          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.66/1.94      inference('sup-', [status(thm)], ['39', '40'])).
% 1.66/1.94  thf('42', plain,
% 1.66/1.94      ((r1_tarski @ 
% 1.66/1.94        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.66/1.94        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.66/1.94      inference('sup-', [status(thm)], ['24', '41'])).
% 1.66/1.94  thf('43', plain,
% 1.66/1.94      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.66/1.94        | ~ (v1_relat_1 @ sk_C))),
% 1.66/1.94      inference('sup+', [status(thm)], ['1', '42'])).
% 1.66/1.94  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.94      inference('demod', [status(thm)], ['9', '10'])).
% 1.66/1.94  thf('45', plain,
% 1.66/1.94      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.66/1.94      inference('demod', [status(thm)], ['43', '44'])).
% 1.66/1.94  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 1.66/1.94  
% 1.66/1.94  % SZS output end Refutation
% 1.66/1.94  
% 1.66/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
