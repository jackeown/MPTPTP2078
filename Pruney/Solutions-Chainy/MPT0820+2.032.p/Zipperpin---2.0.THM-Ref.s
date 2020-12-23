%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KG9dFAUBu9

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 108 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 709 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['8','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('39',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KG9dFAUBu9
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 516 iterations in 0.264s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.72  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.54/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(t19_relset_1, conjecture,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.72        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.54/0.72  thf('0', plain,
% 0.54/0.72      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(commutativity_k2_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.72  thf(t7_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.72  thf('2', plain,
% 0.54/0.72      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.54/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.54/0.72  thf('4', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(cc2_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.72         ((v4_relat_1 @ X19 @ X20)
% 0.54/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.54/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.72  thf('6', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.54/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.72  thf(d18_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ B ) =>
% 0.54/0.72       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      (![X12 : $i, X13 : $i]:
% 0.54/0.72         (~ (v4_relat_1 @ X12 @ X13)
% 0.54/0.72          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.54/0.72          | ~ (v1_relat_1 @ X12))),
% 0.54/0.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(cc2_relat_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ A ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.54/0.72          | (v1_relat_1 @ X10)
% 0.54/0.72          | ~ (v1_relat_1 @ X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.54/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.72  thf(fc6_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.72  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.72  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['8', '13'])).
% 0.54/0.72  thf(t1_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.54/0.72       ( r1_tarski @ A @ C ) ))).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.72         (~ (r1_tarski @ X2 @ X3)
% 0.54/0.72          | ~ (r1_tarski @ X3 @ X4)
% 0.54/0.72          | (r1_tarski @ X2 @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.72  thf('16', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['3', '16'])).
% 0.54/0.72  thf('18', plain,
% 0.54/0.72      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.54/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.72  thf(t8_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.54/0.72       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.72         (~ (r1_tarski @ X7 @ X8)
% 0.54/0.72          | ~ (r1_tarski @ X9 @ X8)
% 0.54/0.72          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.54/0.72      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.54/0.72  thf('20', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         ((r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.72          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.72  thf('21', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (r1_tarski @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.72          (k2_xboole_0 @ X0 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['17', '20'])).
% 0.54/0.72  thf(d6_relat_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ A ) =>
% 0.54/0.72       ( ( k3_relat_1 @ A ) =
% 0.54/0.72         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.72  thf('22', plain,
% 0.54/0.72      (![X16 : $i]:
% 0.54/0.72         (((k3_relat_1 @ X16)
% 0.54/0.72            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.54/0.72          | ~ (v1_relat_1 @ X16))),
% 0.54/0.72      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.54/0.72  thf('23', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.54/0.72  thf('24', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('25', plain,
% 0.54/0.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.72         ((v5_relat_1 @ X19 @ X21)
% 0.54/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.54/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.72  thf('26', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.54/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf(d19_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ B ) =>
% 0.54/0.72       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.72  thf('27', plain,
% 0.54/0.72      (![X14 : $i, X15 : $i]:
% 0.54/0.72         (~ (v5_relat_1 @ X14 @ X15)
% 0.54/0.72          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.54/0.72          | ~ (v1_relat_1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.72  thf('28', plain,
% 0.54/0.72      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.54/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.72  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.72  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.54/0.72      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.72  thf('31', plain,
% 0.54/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.72         (~ (r1_tarski @ X2 @ X3)
% 0.54/0.72          | ~ (r1_tarski @ X3 @ X4)
% 0.54/0.72          | (r1_tarski @ X2 @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.54/0.72      inference('sup-', [status(thm)], ['23', '32'])).
% 0.54/0.72  thf('34', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         ((r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.72          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.72  thf('35', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)) @ 
% 0.54/0.72          (k2_xboole_0 @ X0 @ sk_B))),
% 0.54/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.54/0.72         (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))
% 0.54/0.72        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.72      inference('sup+', [status(thm)], ['22', '35'])).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.72  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.54/0.72        (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.54/0.72      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.54/0.72  thf('40', plain,
% 0.54/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.72         (~ (r1_tarski @ X2 @ X3)
% 0.54/0.72          | ~ (r1_tarski @ X3 @ X4)
% 0.54/0.72          | (r1_tarski @ X2 @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.72  thf('41', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_tarski @ (k3_relat_1 @ sk_C) @ X0)
% 0.54/0.72          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.72  thf('42', plain,
% 0.54/0.72      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '41'])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.72  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
