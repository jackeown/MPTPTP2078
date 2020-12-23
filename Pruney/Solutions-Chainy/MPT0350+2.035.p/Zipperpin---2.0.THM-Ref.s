%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NYZtcYi2YC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 125 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  503 ( 971 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_subset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( k4_subset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = ( k3_subset_1 @ X23 @ ( k1_subset_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,(
    ! [X23: $i] :
      ( X23
      = ( k3_subset_1 @ X23 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','23','27'])).

thf('29',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NYZtcYi2YC
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 231 iterations in 0.120s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.57  thf(t25_subset_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.57         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.57            ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.21/0.57  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k2_subset_1, axiom,
% 0.21/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.57  thf('2', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.57  thf('3', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(dt_k4_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.21/0.57          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 0.21/0.57             (k1_zfmisc_1 @ X16)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.57  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('8', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.21/0.57          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_A @ sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_A @ sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '13'])).
% 0.21/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (((k3_subset_1 @ sk_A @ 
% 0.21/0.57         (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))
% 0.21/0.57         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '13'])).
% 0.21/0.57  thf(d5_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.21/0.57         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf(t46_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.57  thf(t22_subset_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X23 : $i]:
% 0.21/0.57         ((k2_subset_1 @ X23) = (k3_subset_1 @ X23 @ (k1_subset_1 @ X23)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.57  thf('25', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('26', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.57  thf('27', plain, (![X23 : $i]: ((X23) = (k3_subset_1 @ X23 @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.57  thf('28', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '23', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.57         != (k2_subset_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '34'])).
% 0.21/0.57  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k3_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.21/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.21/0.57          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.21/0.57         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.57  thf(t39_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.21/0.57           = (k2_xboole_0 @ X2 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.21/0.57         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '46'])).
% 0.21/0.57  thf('48', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['28', '47'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
