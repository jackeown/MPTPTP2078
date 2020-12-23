%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKyX6dazcP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:03 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 140 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  455 (1050 expanded)
%              Number of equality atoms :   39 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X14 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('42',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKyX6dazcP
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:39:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 543 iterations in 0.256s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.51/0.70  thf(t4_subset_1, axiom,
% 0.51/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (![X23 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.51/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.51/0.70  thf(dt_k2_subset_1, axiom,
% 0.51/0.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X14 : $i]: (m1_subset_1 @ (k2_subset_1 @ X14) @ (k1_zfmisc_1 @ X14))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.51/0.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.51/0.70  thf('2', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.51/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.70  thf('3', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 0.51/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf(t28_subset_1, conjecture,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i,B:$i]:
% 0.51/0.70        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.51/0.70  thf('4', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_k4_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.51/0.70       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.51/0.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.51/0.70          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 0.51/0.70             (k1_zfmisc_1 @ X16)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.51/0.70           (k1_zfmisc_1 @ sk_A))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.51/0.70  thf('8', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 0.51/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k4_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.51/0.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.51/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.51/0.70          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['8', '11'])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['7', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.51/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.51/0.70          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k4_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.51/0.70            = (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.51/0.70         = (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['0', '15'])).
% 0.51/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.51/0.70  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.51/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.51/0.70  thf(t12_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (![X2 : $i, X3 : $i]:
% 0.51/0.70         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.70  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.70  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['19', '20'])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.51/0.70         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['16', '21'])).
% 0.51/0.70  thf('23', plain,
% 0.51/0.70      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['7', '12'])).
% 0.51/0.70  thf(t25_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.51/0.70         ( k2_subset_1 @ A ) ) ))).
% 0.51/0.70  thf('24', plain,
% 0.51/0.70      (![X21 : $i, X22 : $i]:
% 0.51/0.70         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 0.51/0.70            = (k2_subset_1 @ X21))
% 0.51/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.51/0.70  thf('25', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.51/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X21 : $i, X22 : $i]:
% 0.51/0.70         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 0.51/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.51/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.51/0.70         (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))) = (sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '26'])).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['7', '12'])).
% 0.51/0.70  thf(d5_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i]:
% 0.51/0.70         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.51/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.51/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.51/0.70         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.70  thf(t46_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (![X5 : $i, X6 : $i]:
% 0.51/0.70         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.51/0.70      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['31', '32'])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.51/0.70      inference('demod', [status(thm)], ['30', '33'])).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.51/0.70         = (sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['27', '34'])).
% 0.51/0.70  thf('36', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.51/0.70      inference('sup+', [status(thm)], ['22', '35'])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.51/0.70         != (k2_subset_1 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('38', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.51/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.70  thf('39', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.51/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.70  thf('40', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['8', '11'])).
% 0.51/0.70  thf('42', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.70  thf('43', plain, ($false),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['36', '42'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
