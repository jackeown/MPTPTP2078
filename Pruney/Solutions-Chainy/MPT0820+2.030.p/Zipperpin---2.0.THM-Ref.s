%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HjdJytngC5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 111 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  439 ( 722 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['5','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HjdJytngC5
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.14  % Solved by: fo/fo7.sh
% 1.94/2.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.14  % done 2474 iterations in 1.680s
% 1.94/2.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.14  % SZS output start Refutation
% 1.94/2.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.94/2.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.94/2.14  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.14  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.14  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.94/2.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.94/2.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.94/2.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.94/2.14  thf(sk_C_type, type, sk_C: $i).
% 1.94/2.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.94/2.14  thf(t19_relset_1, conjecture,
% 1.94/2.14    (![A:$i,B:$i,C:$i]:
% 1.94/2.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.14       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.94/2.14  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.14    (~( ![A:$i,B:$i,C:$i]:
% 1.94/2.14        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.14          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.94/2.14    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.94/2.14  thf('0', plain,
% 1.94/2.14      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.94/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.14  thf('1', plain,
% 1.94/2.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.94/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.14  thf(cc2_relset_1, axiom,
% 1.94/2.14    (![A:$i,B:$i,C:$i]:
% 1.94/2.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.94/2.14  thf('2', plain,
% 1.94/2.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.94/2.14         ((v5_relat_1 @ X21 @ X23)
% 1.94/2.14          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.94/2.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.94/2.14  thf('3', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.94/2.14      inference('sup-', [status(thm)], ['1', '2'])).
% 1.94/2.14  thf(d19_relat_1, axiom,
% 1.94/2.14    (![A:$i,B:$i]:
% 1.94/2.14     ( ( v1_relat_1 @ B ) =>
% 1.94/2.14       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.94/2.14  thf('4', plain,
% 1.94/2.14      (![X16 : $i, X17 : $i]:
% 1.94/2.14         (~ (v5_relat_1 @ X16 @ X17)
% 1.94/2.14          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.94/2.14          | ~ (v1_relat_1 @ X16))),
% 1.94/2.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.94/2.14  thf('5', plain,
% 1.94/2.14      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.94/2.14      inference('sup-', [status(thm)], ['3', '4'])).
% 1.94/2.14  thf('6', plain,
% 1.94/2.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.94/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.14  thf(cc2_relat_1, axiom,
% 1.94/2.14    (![A:$i]:
% 1.94/2.14     ( ( v1_relat_1 @ A ) =>
% 1.94/2.14       ( ![B:$i]:
% 1.94/2.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.94/2.14  thf('7', plain,
% 1.94/2.14      (![X12 : $i, X13 : $i]:
% 1.94/2.14         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.94/2.14          | (v1_relat_1 @ X12)
% 1.94/2.14          | ~ (v1_relat_1 @ X13))),
% 1.94/2.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.94/2.14  thf('8', plain,
% 1.94/2.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.94/2.14      inference('sup-', [status(thm)], ['6', '7'])).
% 1.94/2.14  thf(fc6_relat_1, axiom,
% 1.94/2.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.94/2.14  thf('9', plain,
% 1.94/2.14      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 1.94/2.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.94/2.14  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 1.94/2.14      inference('demod', [status(thm)], ['8', '9'])).
% 1.94/2.14  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.94/2.14      inference('demod', [status(thm)], ['5', '10'])).
% 1.94/2.14  thf(t12_xboole_1, axiom,
% 1.94/2.14    (![A:$i,B:$i]:
% 1.94/2.14     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.94/2.14  thf('12', plain,
% 1.94/2.14      (![X5 : $i, X6 : $i]:
% 1.94/2.14         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.94/2.14      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.94/2.14  thf('13', plain, (((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 1.94/2.14      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.14  thf(commutativity_k2_xboole_0, axiom,
% 1.94/2.14    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.94/2.14  thf('14', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.14  thf('15', plain, (((k2_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) = (sk_B))),
% 1.94/2.14      inference('demod', [status(thm)], ['13', '14'])).
% 1.94/2.14  thf('16', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.14  thf(t7_xboole_1, axiom,
% 1.94/2.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.94/2.14  thf('17', plain,
% 1.94/2.14      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.94/2.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.94/2.14  thf('18', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.94/2.14      inference('sup+', [status(thm)], ['16', '17'])).
% 1.94/2.14  thf('19', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.14  thf(t11_xboole_1, axiom,
% 1.94/2.14    (![A:$i,B:$i,C:$i]:
% 1.94/2.14     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.94/2.14  thf('20', plain,
% 1.94/2.14      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.94/2.14         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 1.94/2.14      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.94/2.14  thf('21', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.14         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 1.94/2.14      inference('sup-', [status(thm)], ['19', '20'])).
% 1.94/2.14  thf('22', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.14         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.14      inference('sup-', [status(thm)], ['18', '21'])).
% 1.94/2.14  thf('23', plain,
% 1.94/2.14      (![X0 : $i]:
% 1.94/2.14         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.94/2.14      inference('sup+', [status(thm)], ['15', '22'])).
% 1.94/2.14  thf('24', plain,
% 1.94/2.14      (![X5 : $i, X6 : $i]:
% 1.94/2.14         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.94/2.14      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.94/2.14  thf('25', plain,
% 1.94/2.14      (![X0 : $i]:
% 1.94/2.14         ((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))
% 1.94/2.14           = (k2_xboole_0 @ X0 @ sk_B))),
% 1.94/2.14      inference('sup-', [status(thm)], ['23', '24'])).
% 1.94/2.14  thf(d6_relat_1, axiom,
% 1.94/2.14    (![A:$i]:
% 1.94/2.14     ( ( v1_relat_1 @ A ) =>
% 1.94/2.14       ( ( k3_relat_1 @ A ) =
% 1.94/2.14         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.94/2.14  thf('26', plain,
% 1.94/2.14      (![X18 : $i]:
% 1.94/2.14         (((k3_relat_1 @ X18)
% 1.94/2.14            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.94/2.14          | ~ (v1_relat_1 @ X18))),
% 1.94/2.14      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.94/2.14  thf('27', plain,
% 1.94/2.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.94/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.14  thf('28', plain,
% 1.94/2.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.94/2.14         ((v4_relat_1 @ X21 @ X22)
% 1.94/2.14          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.94/2.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.94/2.14  thf('29', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.94/2.14      inference('sup-', [status(thm)], ['27', '28'])).
% 1.94/2.14  thf(d18_relat_1, axiom,
% 1.94/2.14    (![A:$i,B:$i]:
% 1.94/2.14     ( ( v1_relat_1 @ B ) =>
% 1.94/2.14       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.94/2.14  thf('30', plain,
% 1.94/2.14      (![X14 : $i, X15 : $i]:
% 1.94/2.14         (~ (v4_relat_1 @ X14 @ X15)
% 1.94/2.14          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.94/2.14          | ~ (v1_relat_1 @ X14))),
% 1.94/2.14      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.94/2.14  thf('31', plain,
% 1.94/2.14      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.94/2.14      inference('sup-', [status(thm)], ['29', '30'])).
% 1.94/2.14  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.94/2.14      inference('demod', [status(thm)], ['8', '9'])).
% 1.94/2.14  thf('33', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.94/2.14      inference('demod', [status(thm)], ['31', '32'])).
% 1.94/2.14  thf('34', plain,
% 1.94/2.14      (![X5 : $i, X6 : $i]:
% 1.94/2.14         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.94/2.14      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.94/2.14  thf('35', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 1.94/2.14      inference('sup-', [status(thm)], ['33', '34'])).
% 1.94/2.14  thf('36', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.14  thf('37', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 1.94/2.14      inference('demod', [status(thm)], ['35', '36'])).
% 1.94/2.14  thf('38', plain,
% 1.94/2.14      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.94/2.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.94/2.14  thf('39', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.14         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 1.94/2.14      inference('sup-', [status(thm)], ['19', '20'])).
% 1.94/2.14  thf('40', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.14         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 1.94/2.14      inference('sup-', [status(thm)], ['38', '39'])).
% 1.94/2.14  thf('41', plain,
% 1.94/2.14      (![X0 : $i]:
% 1.94/2.14         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.94/2.14      inference('sup+', [status(thm)], ['37', '40'])).
% 1.94/2.14  thf(t9_xboole_1, axiom,
% 1.94/2.14    (![A:$i,B:$i,C:$i]:
% 1.94/2.14     ( ( r1_tarski @ A @ B ) =>
% 1.94/2.14       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.94/2.14  thf('42', plain,
% 1.94/2.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.94/2.14         (~ (r1_tarski @ X9 @ X10)
% 1.94/2.14          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ (k2_xboole_0 @ X10 @ X11)))),
% 1.94/2.14      inference('cnf', [status(esa)], [t9_xboole_1])).
% 1.94/2.14  thf('43', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]:
% 1.94/2.14         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.94/2.14          (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ X1))),
% 1.94/2.14      inference('sup-', [status(thm)], ['41', '42'])).
% 1.94/2.14  thf('44', plain,
% 1.94/2.14      (![X0 : $i]:
% 1.94/2.14         ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 1.94/2.14           (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ (k2_relat_1 @ sk_C)))
% 1.94/2.14          | ~ (v1_relat_1 @ sk_C))),
% 1.94/2.14      inference('sup+', [status(thm)], ['26', '43'])).
% 1.94/2.14  thf('45', plain,
% 1.94/2.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.14  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.94/2.14      inference('demod', [status(thm)], ['8', '9'])).
% 1.94/2.14  thf('47', plain,
% 1.94/2.14      (![X0 : $i]:
% 1.94/2.14         (r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 1.94/2.14          (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.94/2.14      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.94/2.14  thf('48', plain,
% 1.94/2.14      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.94/2.14      inference('sup+', [status(thm)], ['25', '47'])).
% 1.94/2.14  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.94/2.14  
% 1.94/2.14  % SZS output end Refutation
% 1.94/2.14  
% 1.94/2.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
