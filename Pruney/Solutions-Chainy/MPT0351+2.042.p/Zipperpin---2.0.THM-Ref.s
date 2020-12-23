%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMQLvTZo8w

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:02 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  313 ( 481 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X99: $i,X100: $i] :
      ( ( ( k4_subset_1 @ X99 @ X100 @ ( k3_subset_1 @ X99 @ X100 ) )
        = ( k2_subset_1 @ X99 ) )
      | ~ ( m1_subset_1 @ X100 @ ( k1_zfmisc_1 @ X99 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X78: $i] :
      ( ( k2_subset_1 @ X78 )
      = X78 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X99: $i,X100: $i] :
      ( ( ( k4_subset_1 @ X99 @ X100 @ ( k3_subset_1 @ X99 @ X100 ) )
        = X99 )
      | ~ ( m1_subset_1 @ X100 @ ( k1_zfmisc_1 @ X99 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X82: $i,X83: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X82 @ X83 ) @ ( k1_zfmisc_1 @ X82 ) )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X93: $i,X94: $i,X95: $i] :
      ( ~ ( m1_subset_1 @ X93 @ ( k1_zfmisc_1 @ X94 ) )
      | ~ ( m1_subset_1 @ X95 @ ( k1_zfmisc_1 @ X94 ) )
      | ( ( k4_subset_1 @ X94 @ X93 @ X95 )
        = ( k2_xboole_0 @ X93 @ X95 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X79: $i,X80: $i] :
      ( ( ( k3_subset_1 @ X79 @ X80 )
        = ( k4_xboole_0 @ X79 @ X80 ) )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_xboole_0 @ X44 @ ( k4_xboole_0 @ X45 @ X44 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X78: $i] :
      ( ( k2_subset_1 @ X78 )
      = X78 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,(
    ! [X78: $i] :
      ( ( k2_subset_1 @ X78 )
      = X78 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X81: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X81 ) @ ( k1_zfmisc_1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('24',plain,(
    ! [X78: $i] :
      ( ( k2_subset_1 @ X78 )
      = X78 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X81: $i] :
      ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ X81 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('27',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMQLvTZo8w
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.64/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.81  % Solved by: fo/fo7.sh
% 0.64/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.81  % done 842 iterations in 0.360s
% 0.64/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.81  % SZS output start Refutation
% 0.64/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.81  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.64/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.64/0.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.64/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.64/0.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.64/0.81  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.64/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.81  thf(t28_subset_1, conjecture,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.81       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.64/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.81    (~( ![A:$i,B:$i]:
% 0.64/0.81        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.81          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.64/0.81    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.64/0.81  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(t25_subset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.81       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.64/0.81         ( k2_subset_1 @ A ) ) ))).
% 0.64/0.81  thf('1', plain,
% 0.64/0.81      (![X99 : $i, X100 : $i]:
% 0.64/0.81         (((k4_subset_1 @ X99 @ X100 @ (k3_subset_1 @ X99 @ X100))
% 0.64/0.81            = (k2_subset_1 @ X99))
% 0.64/0.81          | ~ (m1_subset_1 @ X100 @ (k1_zfmisc_1 @ X99)))),
% 0.64/0.81      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.64/0.81  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.64/0.81  thf('2', plain, (![X78 : $i]: ((k2_subset_1 @ X78) = (X78))),
% 0.64/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.81  thf('3', plain,
% 0.64/0.81      (![X99 : $i, X100 : $i]:
% 0.64/0.81         (((k4_subset_1 @ X99 @ X100 @ (k3_subset_1 @ X99 @ X100)) = (X99))
% 0.64/0.81          | ~ (m1_subset_1 @ X100 @ (k1_zfmisc_1 @ X99)))),
% 0.64/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.81  thf('4', plain,
% 0.64/0.81      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['0', '3'])).
% 0.64/0.81  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(dt_k3_subset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.81       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.81  thf('6', plain,
% 0.64/0.81      (![X82 : $i, X83 : $i]:
% 0.64/0.81         ((m1_subset_1 @ (k3_subset_1 @ X82 @ X83) @ (k1_zfmisc_1 @ X82))
% 0.64/0.81          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ X82)))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.64/0.81  thf('7', plain,
% 0.64/0.81      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.64/0.81  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(redefinition_k4_subset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.64/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.64/0.81       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.64/0.81  thf('9', plain,
% 0.64/0.81      (![X93 : $i, X94 : $i, X95 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X93 @ (k1_zfmisc_1 @ X94))
% 0.64/0.81          | ~ (m1_subset_1 @ X95 @ (k1_zfmisc_1 @ X94))
% 0.64/0.81          | ((k4_subset_1 @ X94 @ X93 @ X95) = (k2_xboole_0 @ X93 @ X95)))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.64/0.81  thf('10', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.64/0.81  thf('11', plain,
% 0.64/0.81      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.64/0.81         = (k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['7', '10'])).
% 0.64/0.81  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(d5_subset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.81       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.64/0.81  thf('13', plain,
% 0.64/0.81      (![X79 : $i, X80 : $i]:
% 0.64/0.81         (((k3_subset_1 @ X79 @ X80) = (k4_xboole_0 @ X79 @ X80))
% 0.64/0.81          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ X79)))),
% 0.64/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.64/0.81  thf('14', plain,
% 0.64/0.81      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.64/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.81  thf(t39_xboole_1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.64/0.81  thf('15', plain,
% 0.64/0.81      (![X44 : $i, X45 : $i]:
% 0.64/0.81         ((k2_xboole_0 @ X44 @ (k4_xboole_0 @ X45 @ X44))
% 0.64/0.81           = (k2_xboole_0 @ X44 @ X45))),
% 0.64/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.64/0.81  thf('16', plain,
% 0.64/0.81      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.64/0.81         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.64/0.81      inference('sup+', [status(thm)], ['14', '15'])).
% 0.64/0.81  thf('17', plain,
% 0.64/0.81      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.64/0.81         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['11', '16'])).
% 0.64/0.81  thf('18', plain, (((sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.64/0.81      inference('sup+', [status(thm)], ['4', '17'])).
% 0.64/0.81  thf('19', plain,
% 0.64/0.81      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 0.64/0.81         != (k2_subset_1 @ sk_A))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('20', plain, (![X78 : $i]: ((k2_subset_1 @ X78) = (X78))),
% 0.64/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.81  thf('21', plain, (![X78 : $i]: ((k2_subset_1 @ X78) = (X78))),
% 0.64/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.81  thf('22', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.64/0.81  thf(dt_k2_subset_1, axiom,
% 0.64/0.81    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.64/0.81  thf('23', plain,
% 0.64/0.81      (![X81 : $i]: (m1_subset_1 @ (k2_subset_1 @ X81) @ (k1_zfmisc_1 @ X81))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.64/0.81  thf('24', plain, (![X78 : $i]: ((k2_subset_1 @ X78) = (X78))),
% 0.64/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.81  thf('25', plain, (![X81 : $i]: (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ X81))),
% 0.64/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.64/0.81  thf('26', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.64/0.81  thf('27', plain,
% 0.64/0.81      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['25', '26'])).
% 0.64/0.81  thf('28', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['22', '27'])).
% 0.64/0.81  thf('29', plain, ($false),
% 0.64/0.81      inference('simplify_reflect-', [status(thm)], ['18', '28'])).
% 0.64/0.81  
% 0.64/0.81  % SZS output end Refutation
% 0.64/0.81  
% 0.64/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
