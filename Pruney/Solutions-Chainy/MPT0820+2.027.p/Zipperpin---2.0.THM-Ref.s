%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KtRsCk8VRl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:51 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 116 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  451 ( 781 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( ( k3_relat_1 @ X21 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X21 ) @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KtRsCk8VRl
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 386 iterations in 0.200s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(t19_relset_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         ((v4_relat_1 @ X24 @ X25)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('4', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(d18_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         (~ (v4_relat_1 @ X17 @ X18)
% 0.47/0.66          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.47/0.66          | ~ (v1_relat_1 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.47/0.66          | (v1_relat_1 @ X15)
% 0.47/0.66          | ~ (v1_relat_1 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.66  thf(fc6_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.66  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.47/0.66      inference('demod', [status(thm)], ['6', '11'])).
% 0.47/0.66  thf(t36_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.47/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.66  thf(t1_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.66       ( r1_tarski @ A @ C ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.47/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.47/0.66          | (r1_tarski @ X2 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k4_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '15'])).
% 0.47/0.66  thf(t44_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.47/0.66       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.66         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.47/0.66          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['1', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.47/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.66         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.47/0.66          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf(t8_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.47/0.66       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X10 @ X11)
% 0.47/0.66          | ~ (r1_tarski @ X12 @ X11)
% 0.47/0.66          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.66          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.47/0.66          (k2_xboole_0 @ sk_A @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['19', '24'])).
% 0.47/0.66  thf(d6_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( k3_relat_1 @ A ) =
% 0.47/0.66         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X21 : $i]:
% 0.47/0.66         (((k3_relat_1 @ X21)
% 0.47/0.66            = (k2_xboole_0 @ (k1_relat_1 @ X21) @ (k2_relat_1 @ X21)))
% 0.47/0.66          | ~ (v1_relat_1 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         ((v5_relat_1 @ X24 @ X26)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('30', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf(d19_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         (~ (v5_relat_1 @ X19 @ X20)
% 0.47/0.66          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.47/0.66          | ~ (v1_relat_1 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.66         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.47/0.66          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['27', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.66          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)) @ 
% 0.47/0.66          (k2_xboole_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.47/0.66         (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.66      inference('sup+', [status(thm)], ['26', '41'])).
% 0.47/0.66  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.47/0.66        (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.47/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.47/0.66          | (r1_tarski @ X2 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k3_relat_1 @ sk_C) @ X0)
% 0.47/0.66          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '46'])).
% 0.47/0.66  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.51/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
